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

(** For either role, a stored server Finished (sent or received) is the
    correct MAC under the server handshake traffic secret over the transcript
    up to the CertificateVerify, and a stored client Finished is the correct
    MAC under the client handshake traffic secret over the transcript up to
    the server Finished. *)
let fin_ok (m:connection_model) : prop =
  let hs = m.model_handshake in
  (match hs.hs_server_finished with
   | None -> True
   | Some sf ->
     (match hs.hs_keys.ks_server_handshake_traffic, th_at TH_before_SF m with
      | Some shs, Some th -> H.verify_finished shs.traffic_secret (Tr.hash th) sf == true
      | _, _ -> False)) /\
  (match hs.hs_client_finished with
   | None -> True
   | Some cf ->
     (match hs.hs_keys.ks_client_handshake_traffic, th_at TH_SF m with
      | Some chs, Some th -> H.verify_finished chs.traffic_secret (Tr.hash th) cf == true
      | _, _ -> False))

(** The handshake secret is derived only with the shared secret, and the
    handshake traffic secrets are the ones at the handshake secret and the
    transcript up to the ServerHello. *)
let hs_secrets_ok (m:connection_model) : prop =
  let keys = m.model_handshake.hs_keys in
  (None? keys.ks_shared_secret ==> None? keys.ks_handshake_secret) /\
  (match keys.ks_server_handshake_traffic with
   | None -> True
   | Some shs ->
     (match keys.ks_handshake_secret, th_at TH_SH m with
      | Some hsec, Some th ->
        shs.traffic_secret == K.server_handshake_traffic_secret hsec (Tr.hash th)
      | _, _ -> False)) /\
  (match keys.ks_client_handshake_traffic with
   | None -> True
   | Some chs ->
     (match keys.ks_handshake_secret, th_at TH_SH m with
      | Some hsec, Some th ->
        chs.traffic_secret == K.client_handshake_traffic_secret hsec (Tr.hash th)
      | _, _ -> False))

let fin_inv (m:connection_model) : prop =
  let role = m.model_config.config_role in
  application_traffic_install_checkpoint_ready_for_role role m /\
  (role == ClientEndpoint ==> client_cv_ok m) /\
  hs_secrets_ok m /\ fin_ok m

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
let lemma_step_checkpoint (m0:connection_model) (ev:conn_event) (m1:connection_model)
  : Lemma
      (requires fin_inv m0 /\ legal_event m0 ev /\ step_model m0 ev == Some m1)
      (ensures m1.model_config == m0.model_config /\
               application_traffic_install_checkpoint_ready_for_role m0.model_config.config_role m1)
=
  lemma_step_model_preserves_config m0 ev m1;
  lemma_step_model_preserves_application_traffic_install_checkpoint_ready_for_role
    m0.model_config.config_role m0 ev m1

let lemma_step_client_cv (m0:connection_model) (ev:conn_event) (m1:connection_model)
  : Lemma
      (requires fin_inv m0 /\ legal_event m0 ev /\ step_model m0 ev == Some m1 /\
                m0.model_config.config_role == ClientEndpoint)
      (ensures client_cv_ok m1)
=
  lemma_step_checkpoint m0 ev m1;
  match ev with
  | ConnLocalEvent local -> ()
  | ConnNetworkEvent msg -> ()
  | ConnProtectedHandshake step -> ()

let lemma_step_hs_secrets (m0:connection_model) (ev:conn_event) (m1:connection_model)
  : Lemma
      (requires fin_inv m0 /\ legal_event m0 ev /\ step_model m0 ev == Some m1)
      (ensures hs_secrets_ok m1)
=
  lemma_step_checkpoint m0 ev m1;
  match ev with
  | ConnLocalEvent local -> ()
  | ConnNetworkEvent msg -> ()
  | ConnProtectedHandshake step -> ()

let lemma_step_fin_ok (m0:connection_model) (ev:conn_event) (m1:connection_model)
  : Lemma
      (requires fin_inv m0 /\ legal_event m0 ev /\ step_model m0 ev == Some m1)
      (ensures fin_ok m1)
=
  lemma_step_checkpoint m0 ev m1;
  match ev with
  | ConnLocalEvent local -> ()
  | ConnNetworkEvent msg -> ()
  | ConnProtectedHandshake step -> ()

let lemma_step_fin_inv (m0:connection_model) (ev:conn_event) (m1:connection_model)
  : Lemma
      (requires fin_inv m0 /\ legal_event m0 ev /\ step_model m0 ev == Some m1)
      (ensures fin_inv m1)
=
  lemma_step_checkpoint m0 ev m1;
  if m0.model_config.config_role = ClientEndpoint then lemma_step_client_cv m0 ev m1;
  lemma_step_hs_secrets m0 ev m1;
  lemma_step_fin_ok m0 ev m1
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

let lemma_hs_secret_at_index (st:connection_state) (label:traffic_label)
  : Lemma
      (requires
        connection_state_consistent st /\
        Some? st.cs_model.model_handshake.hs_keys.ks_shared_secret /\
        Some? (state_kex_index st) /\
        Some? (hs_traffic st.cs_model.model_handshake.hs_keys label) /\
        Some? (th_at TH_SH st.cs_model))
      (ensures (
        let keys = st.cs_model.model_handshake.hs_keys in
        (Some?.v (hs_traffic keys label)).traffic_secret ==
          real_traffic (Some?.v keys.ks_shared_secret)
            (hs_index (Some?.v (state_kex_index st)) label
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
            session_traffic_index x e l == state_traffic_index st e l) /\
          (match st.cs_model.model_handshake.hs_client_finished with
           | Some cf ->
             let (gst'', r') = step_client_finished (real_oracle dhe) gst' n (finished_msg cf) in
             r' == RAccept true /\
             session_at gst'' n ==
               Some (ServerSession (k.kx_group, id, SAccepted (k, f_th_sh f, f_th_sf f)))
           | None -> True)
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
  lemma_hs_secret_at_index st ServerTraffic;
  let Some shs = hs.hs_keys.ks_server_handshake_traffic in
  let fk = K.finished_key shs.traffic_secret in
  Seq.lemma_eq_elim sf (K.finished_verify_data shs.traffic_secret (Tr.hash (f_th_pre f)));
  assert (sf == mac fk (f_th_pre f));
  let n = L.length gst.sessions in
  lemma_snoc_index gst.sessions
    (ServerSession (k.kx_group, id, SWaitFinished (k, f_th_sh f, f_th_sf f))) n;
  lemma_session_indices st k (f_th_sh f) (f_th_sf f)
    (ServerSession (k.kx_group, id, SWaitFinished (k, f_th_sh f, f_th_sf f)));
  match hs.hs_client_finished with
  | Some cf ->
    lemma_hs_secret_at_index st ClientTraffic;
    let Some chs = hs.hs_keys.ks_client_handshake_traffic in
    Seq.lemma_eq_elim cf (K.finished_verify_data chs.traffic_secret (Tr.hash (f_th_sf f)));
    assert (cf == mac (K.finished_key chs.traffic_secret) (f_th_sf f));
    assert (real_oracle dhe (IdxFinishedKey (hs_index k ClientTraffic (f_th_sh f))) ==
            Some (K.finished_key chs.traffic_secret <: B.bytes));
    let gst' = fst (step_start_server cs (real_oracle dhe) gst k.kx_group id
                      k.kx_client_share f.f_ch f.f_sh f.f_ee_cert f.f_cv) in
    lemma_update_nth_index gst'.sessions n
      (ServerSession (k.kx_group, id, SAccepted (k, f_th_sh f, f_th_sf f))) n
  | None -> ()


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
            (let (gst2, r2) =
               step_server_flight_with sc (real_oracle dhe) gst1 s f.f_ee_cert f.f_cv f.f_sf in
             (match session_at gst2 s with
              | Some x ->
                x == ClientSession (k.kx_group, peer,
                       CAccepted (k, f_th_sh f, f_th_sf f, not (L.mem peer gst1.corrupted))) /\
                (forall (e:traffic_epoch) (l:traffic_label).
                  session_traffic_index x e l == state_traffic_index st e l)
              | None -> False) /\
             (match st.cs_model.model_handshake.hs_client_finished with
              | Some cf -> r2 == RClientFinished (finished_msg cf)
              | None -> True)))
        | _, _ -> False))
=
  let hs = st.cs_model.model_handshake in
  lemma_consistent_fin_inv st;
  lemma_client_secrets_at_index st;
  let Some k = state_kex_index st in
  assert (Some? (spec_flight_of hs));
  let Some f = spec_flight_of hs in
  lemma_flight_transcripts hs;
  let Some sf = hs.hs_server_finished in
  lemma_hs_secret_at_index st ServerTraffic;
  let Some shs = hs.hs_keys.ks_server_handshake_traffic in
  Seq.lemma_eq_elim sf (K.finished_verify_data shs.traffic_secret (Tr.hash (f_th_pre f)));
  assert (sf == mac (K.finished_key shs.traffic_secret) (f_th_pre f));
  assert (real_oracle dhe (IdxFinishedKey (hs_index k ServerTraffic (f_th_sh f))) ==
          Some (K.finished_key shs.traffic_secret <: B.bytes));
  (match hs.hs_client_finished with
   | Some cf ->
     lemma_hs_secret_at_index st ClientTraffic;
     let Some chs = hs.hs_keys.ks_client_handshake_traffic in
     Seq.lemma_eq_elim cf (K.finished_verify_data chs.traffic_secret (Tr.hash (f_th_sf f)));
     assert (cf == mac (K.finished_key chs.traffic_secret) (f_th_sf f));
     assert (real_oracle dhe (IdxFinishedKey (hs_index k ClientTraffic (f_th_sh f))) ==
             Some (K.finished_key chs.traffic_secret <: B.bytes))
   | None -> ());
  lemma_update_nth_index gst.sessions s
    (ClientSession (k.kx_group, peer, CWaitFlight (k, f_th_sh f))) s;
  let gst1 = fst (step_server_hello cs gst s k.kx_server_share f.f_sh) in
  let x = ClientSession (k.kx_group, peer,
            CAccepted (k, f_th_sh f, f_th_sf f, not (L.mem peer gst1.corrupted))) in
  lemma_update_nth_index gst1.sessions s x s;
  lemma_session_indices st k (f_th_sh f) (f_th_sf f) x
