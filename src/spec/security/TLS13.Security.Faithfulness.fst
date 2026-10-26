module TLS13.Security.Faithfulness

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module H = TLS13.Handshake.Spec
module K = TLS13.Keys
module L = FStar.List.Tot
module M = TLS13.Messages
module RTC = FStar.ReflexiveTransitiveClosure
module Tr = TLS13.Transcript
module W = TLS13.Wire.Spec

open TLS13.Spec.StateMachine
open TLS13.Spec.StateMachine.KeyIdentifiers
open TLS13.Spec.StateMachine.Reachability
open TLS13.Spec.StateMachine.Correspondence
open TLS13.ConnectionState.Lemmas
open TLS13.Security.Index
open TLS13.Security.KeyIndex
open TLS13.Security.Oracle
open TLS13.Security.Game

friend TLS13.ConnectionState.Lemmas

(** {1 A reachability invariant for signatures and Finished} *)

(** A client that has verified the CertificateVerify holds a valid signature
    by the validated peer over the transcript up to the Certificate; before
    verification, the pending signature input is that transcript's.  Accepting
    the server Finished requires a verified CertificateVerify. *)
let client_cv_ok (m:connection_model) : prop =
  let hs = m.model_handshake in
  (hs.hs_certificate_verify_verified ==>
    (match hs.hs_validated_peer, hs.hs_certificate_verify, th_at TH_before_CV m with
     | Some peer, Some cv, Some th -> H.verify_certificate_verify peer (Tr.hash th) cv == true
     | _, _, _ -> False)) /\
  ((m.model_control == ControlHandshaking HsCertificateVerifyVerified \/
    m.model_control == ControlHandshaking HsServerFinishedReceived) ==>
    hs.hs_certificate_verify_verified) /\
  (hs.hs_server_finished_verified ==>
    hs.hs_certificate_verify_verified /\ Some? hs.hs_server_finished) /\
  (m.model_control == ControlHandshaking HsCertificateVerifyReceived ==>
    (match th_at TH_before_CV m with
     | Some th ->
       hs.hs_buffers.hb_certificate_verify_input ==
         Some (H.certificate_verify_input (Tr.hash th))
     | None -> False))

(** A server's Finished is the correct MAC under its handshake traffic
    secret over the transcript up to the CertificateVerify. *)
let server_fin_ok (m:connection_model) : prop =
  let hs = m.model_handshake in
  match hs.hs_server_finished with
  | None -> True
  | Some sf ->
    (match hs.hs_keys.ks_server_handshake_traffic, th_at TH_before_SF m with
     | Some shs, Some th -> H.verify_finished shs.traffic_secret (Tr.hash th) sf == true
     | _, _ -> False)

(** A server's handshake write secret is the one at its handshake secret and
    the transcript up to the ServerHello. *)
let server_hs_secret_ok (m:connection_model) : prop =
  let keys = m.model_handshake.hs_keys in
  match keys.ks_server_handshake_traffic with
  | None -> True
  | Some shs ->
    (match keys.ks_handshake_secret, th_at TH_SH m with
     | Some hsec, Some th ->
       shs.traffic_secret == K.server_handshake_traffic_secret hsec (Tr.hash th)
     | _, _ -> False)

let fin_inv (m:connection_model) : prop =
  let role = m.model_config.config_role in
  application_traffic_install_checkpoint_ready_for_role role m /\
  (role == ClientEndpoint ==> client_cv_ok m) /\
  (role == ServerEndpoint ==> server_hs_secret_ok m /\ server_fin_ok m)

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
let lemma_step_fin_inv (m0:connection_model) (ev:conn_event) (m1:connection_model)
  : Lemma
      (requires fin_inv m0 /\ legal_event m0 ev /\ step_model m0 ev == Some m1)
      (ensures fin_inv m1)
=
  let role = m0.model_config.config_role in
  lemma_step_model_preserves_config m0 ev m1;
  lemma_step_model_preserves_application_traffic_install_checkpoint_ready_for_role role m0 ev m1;
  match ev with
  | ConnLocalEvent local -> ()
  | ConnNetworkEvent msg -> ()
  | ConnProtectedHandshake step -> ()
#pop-options

let lemma_initial_fin_inv (cfg:connection_config)
  : Lemma (fin_inv (initial cfg).cs_model)
= ()

let lemma_single_step_fin_inv (x y:connection_state)
  : Lemma
      (requires fin_inv x.cs_model /\ connection_state_single_step x y)
      (ensures fin_inv y.cs_model)
=
  let aux (delta:connection_delta)
    : Lemma (legal_connection_delta x delta y ==> fin_inv y.cs_model)
    = FStar.Classical.move_requires (lemma_step_fin_inv x.cs_model delta.delta_event) y.cs_model
  in
  FStar.Classical.forall_intro aux

let lemma_consistent_fin_inv (st:connection_state)
  : Lemma (requires connection_state_consistent st) (ensures fin_inv st.cs_model)
=
  let p (st:connection_state) : prop = fin_inv st.cs_model in
  lemma_initial_fin_inv st.cs_model.model_config;
  let aux (x y:connection_state)
    : Lemma (p x /\ connection_state_single_step x y ==> p y)
    = FStar.Classical.move_requires (lemma_single_step_fin_inv x) y
  in
  FStar.Classical.forall_intro_2 aux;
  RTC.stable_on_closure connection_state_single_step p ()

(** The game's transcripts are the spec's checkpoints. *)
let lemma_flight_transcripts (hs:handshake_state)
  : Lemma
      (requires Some? (spec_flight_of hs))
      (ensures (
        let f = Some?.v (spec_flight_of hs) in
        transcript_checkpoint_bytes TH_SH hs == Some (f_th_sh f) /\
        transcript_checkpoint_bytes TH_before_CV hs == Some (f_th_cv f) /\
        transcript_checkpoint_bytes TH_before_SF hs == Some (f_th_pre f) /\
        transcript_checkpoint_bytes TH_SF hs == Some (f_th_sf f)))
=
  let f = Some?.v (spec_flight_of hs) in
  match hs.hs_encrypted_extensions, hs.hs_certificate with
  | Some ee, Some cert ->
    Seq.append_assoc (f_th_sh f)
      (W.serialize_handshake (M.EncryptedExtensions ee))
      (W.serialize_handshake (M.Certificate cert))

(** The traffic indices of a game session at the spec's transcripts are the
    spec's indices. *)
let lemma_session_indices
  (st:connection_state) (k:kex_index) (th_sh th_sf:B.bytes) (x:session)
  : Lemma
      (requires
        state_kex_index st == Some k /\
        transcript_checkpoint_bytes TH_SH st.cs_model.model_handshake == Some th_sh /\
        transcript_checkpoint_bytes TH_SF st.cs_model.model_handshake == Some th_sf /\
        (match x with
         | ClientSession (_, _, CAccepted (k', th_sh', th_sf', _))
         | ServerSession (_, _, SWaitFinished (k', th_sh', th_sf'))
         | ServerSession (_, _, SAccepted (k', th_sh', th_sf')) ->
           k' == k /\ th_sh' == th_sh /\ th_sf' == th_sf
         | _ -> False))
      (ensures
        forall (e:traffic_epoch) (l:traffic_label).
          session_traffic_index x e l == state_traffic_index st e l)
= ()

(** {1 Server} *)

(** A server's handshake write secret is the real one at its index. *)
let lemma_server_hs_secret_at_index (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == ServerEndpoint /\
        Some? st.cs_model.model_handshake.hs_keys.ks_shared_secret /\
        Some? (state_kex_index st) /\
        Some? st.cs_model.model_handshake.hs_keys.ks_server_handshake_traffic /\
        Some? (th_at TH_SH st.cs_model))
      (ensures (
        let keys = st.cs_model.model_handshake.hs_keys in
        (Some?.v keys.ks_server_handshake_traffic).traffic_secret ==
          real_traffic (Some?.v keys.ks_shared_secret)
            (hs_index (Some?.v (state_kex_index st)) ServerTraffic
                      (Some?.v (th_at TH_SH st.cs_model)))))
=
  lemma_consistent_fin_inv st;
  lemma_base_secrets_at_index st

let lemma_server_faithful
  (st:connection_state) (cs:coins) (dhe:dhe_table) (gst:game_state) (id:ident)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == ServerEndpoint /\
        ~(ControlFailed? st.cs_model.model_control) /\
        Some? st.cs_model.model_handshake.hs_server_finished /\
        Some? st.cs_model.model_handshake.hs_keys.ks_shared_secret /\
        (match state_kex_index st with
         | Some k ->
           server_kex_private_of st k.kx_group == Some (cs (L.length gst.sessions)) /\
           dhe k == Some (Some?.v st.cs_model.model_handshake.hs_keys.ks_shared_secret <: B.bytes)
         | None -> False))
      (ensures (
        match state_kex_index st, spec_flight_of st.cs_model.model_handshake with
        | Some k, Some f ->
          let n = L.length gst.sessions in
          let (gst', r) =
            step_start_server cs (real_oracle dhe) gst k.kx_group id
              k.kx_client_share f.f_ch f.f_sh f.f_ee_cert f.f_cv in
          let x = ServerSession (k.kx_group, id, SWaitFinished (k, f_th_sh f, f_th_sf f)) in
          r == RServerFlight (k.kx_server_share, f.f_sf) /\
          session_at gst' n == Some x /\
          (forall (e:traffic_epoch) (l:traffic_label).
            session_traffic_index x e l == state_traffic_index st e l)
        | _, _ -> False))
=
  let hs = st.cs_model.model_handshake in
  lemma_consistent_fin_inv st;
  lemma_server_secrets_at_index st;
  let Some k = state_kex_index st in
  let Some sf = hs.hs_server_finished in
  assert (Some? (spec_flight_of hs));
  let Some f = spec_flight_of hs in
  lemma_flight_transcripts hs;
  lemma_server_hs_secret_at_index st;
  let Some shs = hs.hs_keys.ks_server_handshake_traffic in
  let fk = K.finished_key shs.traffic_secret in
  Seq.lemma_eq_elim sf (K.finished_verify_data shs.traffic_secret (Tr.hash (f_th_pre f)));
  assert (sf == mac fk (f_th_pre f));
  let n = L.length gst.sessions in
  lemma_snoc_index gst.sessions
    (ServerSession (k.kx_group, id, SWaitFinished (k, f_th_sh f, f_th_sf f))) n;
  lemma_session_indices st k (f_th_sh f) (f_th_sf f)
    (ServerSession (k.kx_group, id, SWaitFinished (k, f_th_sh f, f_th_sf f)))


(** {1 Client} *)

let lemma_client_faithful
  (st:connection_state) (cs:coins) (dhe:dhe_table) (gst:game_state) (s:nat) (peer:ident)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == ClientEndpoint /\
        st.cs_model.model_handshake.hs_server_finished_verified /\
        Some? st.cs_model.model_handshake.hs_keys.ks_shared_secret /\
        (match state_kex_index st, st.cs_model.model_handshake.hs_client_hello with
         | Some k, Some ch ->
           client_kex_private st k.kx_group == Some (cs s) /\
           dhe k == Some (Some?.v st.cs_model.model_handshake.hs_keys.ks_shared_secret <: B.bytes) /\
           session_at gst s ==
             Some (ClientSession (k.kx_group, peer,
                     CWaitServerHello (W.serialize_handshake (M.ClientHello ch))))
         | _, _ -> False))
      (ensures (
        match state_kex_index st, spec_flight_of st.cs_model.model_handshake with
        | Some k, Some f ->
          let (gst1, r1) = step_server_hello cs gst s k.kx_server_share f.f_sh in
          r1 == ROk /\
          session_at gst1 s == Some (ClientSession (k.kx_group, peer, CWaitFlight (k, f_th_sh f))) /\
          client_signature_valid st.cs_model.model_handshake f /\
          (forall (sc:sig_check).
            sc gst1 peer k (f_th_cv f) f.f_cv == true ==>
            (match session_at
                     (fst (step_server_flight_with sc (real_oracle dhe) gst1 s
                             f.f_ee_cert f.f_cv f.f_sf)) s with
             | Some x ->
               x == ClientSession (k.kx_group, peer,
                      CAccepted (k, f_th_sh f, f_th_sf f, not (L.mem peer gst1.corrupted))) /\
               (forall (e:traffic_epoch) (l:traffic_label).
                 session_traffic_index x e l == state_traffic_index st e l)
             | None -> False))
        | _, _ -> False))
=
  let hs = st.cs_model.model_handshake in
  lemma_consistent_fin_inv st;
  lemma_client_secrets_at_index st;
  let Some k = state_kex_index st in
  assert (Some? (spec_flight_of hs));
  let Some f = spec_flight_of hs in
  lemma_flight_transcripts hs;
  lemma_update_nth_index gst.sessions s
    (ClientSession (k.kx_group, peer, CWaitFlight (k, f_th_sh f))) s;
  let gst1 = fst (step_server_hello cs gst s k.kx_server_share f.f_sh) in
  let x = ClientSession (k.kx_group, peer,
            CAccepted (k, f_th_sh f, f_th_sf f, not (L.mem peer gst1.corrupted))) in
  lemma_update_nth_index gst1.sessions s x s;
  lemma_session_indices st k (f_th_sh f) (f_th_sf f) x
