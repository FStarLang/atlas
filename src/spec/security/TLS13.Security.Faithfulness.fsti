module TLS13.Security.Faithfulness

(**
  Faithfulness of the key-indistinguishability game
  ([TLS13.Security.Game]) to the spec state machine: a reachable spec
  endpoint is a run of the corresponding honest game session against the
  real oracle.  Concretely,

  * the transcripts the game computes from the serialized messages are the
    spec's transcript checkpoints, so the game's traffic indices are the
    spec's ([state_traffic_index]) and the game's keys are the spec's keys;
  * a server's Finished is the game's MAC under the real finished key;
  * a client accepts a CertificateVerify only if it is a valid signature by
    the validated peer over the game's CertificateVerify transcript (the
    "real" signature check of [Game.step_server_flight_with]).

  The spec does not check a received Finished on its reachable paths, nor
  pin a client's own sent Finished; the game is weakened accordingly (see
  the design document).
**)

module B = TLS13.Bytes
module H = TLS13.Handshake.Spec
module L = FStar.List.Tot
module M = TLS13.Messages
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

(** A transcript checkpoint of a model. *)
let th_at (c:transcript_checkpoint) (m:connection_model) : GTot (option B.bytes) =
  transcript_checkpoint_bytes c m.model_handshake

(** {1 The spec's flight in game form} *)

(** The handshake messages of a completed server flight, serialized as the
    game's queries carry them. *)
type spec_flight = {
  f_ch: B.bytes;
  f_sh: B.bytes;
  f_ee_cert: B.bytes;    (* EncryptedExtensions, Certificate *)
  f_cv: B.bytes;
  f_sf: B.bytes;         (* the server Finished message *)
}

let spec_flight_of (hs:handshake_state) : GTot (option spec_flight) =
  match hs.hs_client_hello, hs.hs_server_hello, hs.hs_encrypted_extensions,
        hs.hs_certificate, hs.hs_certificate_verify, hs.hs_server_finished with
  | Some ch, Some sh, Some ee, Some cert, Some cv, Some sf ->
    Some {
      f_ch = W.serialize_handshake (M.ClientHello ch);
      f_sh = W.serialize_handshake (M.ServerHello sh);
      f_ee_cert = B.append (W.serialize_handshake (M.EncryptedExtensions ee))
                           (W.serialize_handshake (M.Certificate cert));
      f_cv = W.serialize_handshake (M.CertificateVerify cv);
      f_sf = finished_msg sf;
    }
  | _, _, _, _, _, _ -> None

let f_th_sh (f:spec_flight) : B.bytes = B.append f.f_ch f.f_sh
let f_th_cv (f:spec_flight) : B.bytes = B.append (f_th_sh f) f.f_ee_cert
let f_th_pre (f:spec_flight) : B.bytes = B.append (f_th_cv f) f.f_cv
let f_th_sf (f:spec_flight) : B.bytes = B.append (f_th_pre f) f.f_sf

(** A client that accepted the server Finished holds a CertificateVerify that
    is a valid signature by the validated peer over the game's
    CertificateVerify transcript. *)
let client_signature_valid (hs:handshake_state) (f:spec_flight) : GTot prop =
  match hs.hs_validated_peer, hs.hs_certificate_verify with
  | Some peer, Some cv ->
    f.f_cv == W.serialize_handshake (M.CertificateVerify cv) /\
    H.verify_certificate_verify peer (Tr.hash (f_th_cv f)) cv == true
  | _, _ -> False

(** The game's transcripts are the spec's checkpoints. *)
val lemma_flight_transcripts (hs:handshake_state)
  : Lemma
      (requires Some? (spec_flight_of hs))
      (ensures (
        let f = Some?.v (spec_flight_of hs) in
        transcript_checkpoint_bytes TH_SH hs == Some (f_th_sh f) /\
        transcript_checkpoint_bytes TH_before_CV hs == Some (f_th_cv f) /\
        transcript_checkpoint_bytes TH_before_SF hs == Some (f_th_pre f) /\
        transcript_checkpoint_bytes TH_SF hs == Some (f_th_sf f)))

(** A server's handshake write secret is the real one at its index (the
    key-index lemma covers only keys and IVs). *)
val lemma_server_hs_secret_at_index (st:connection_state)
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

(** {1 Faithfulness} *)

(** A reachable server that has sent its Finished is an honest game server
    session run on the spec's messages against the real oracle: the game
    answers with the spec's server share and Finished message, and the
    session's traffic indices are the spec's.  Coins of session [n] are the
    server's ephemeral key. *)
val lemma_server_faithful
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

(** A reachable client that accepted the server Finished is an honest game
    client session run on the spec's messages against the real oracle: the
    session reaches [CAccepted] at the spec's transcripts under any signature
    decision that accepts the CertificateVerify, and the spec's
    CertificateVerify is a valid signature by the validated peer over the
    game's transcript -- so the real signature check accepts it. *)
val lemma_client_faithful
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
