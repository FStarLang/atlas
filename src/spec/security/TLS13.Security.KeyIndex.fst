module TLS13.Security.KeyIndex

(**
  Key-index lemma: in every reachable connection state, each secret of the
  key schedule and each installed traffic key / IV is the real value
  ([TLS13.Security.Index.real_secret]) at its public index, computed from the
  session's (EC)DHE output -- and that output is the Diffie-Hellman of the
  session's own ephemeral private key with the peer's share as it appears on
  the wire.

  This is the bridge between the relational state machine and the
  index-based security games: the games may replace [real_secret] at honest
  indices by random values, and this lemma is what lets a real-world game
  execution be read back as legal spec executions.  Statements are for the
  (EC)DH groups (X25519 and P-256); the X25519MLKEM768 hybrid is out of scope.
**)

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module K = TLS13.Keys
module RTC = FStar.ReflexiveTransitiveClosure
module Seq = FStar.Seq

open TLS13.Spec.StateMachine
open TLS13.Spec.StateMachine.KeyIdentifiers
open TLS13.Spec.StateMachine.Reachability
open TLS13.Spec.StateMachine.Correspondence
open TLS13.Spec.StateMachine.KeyMaterial
open TLS13.Spec.StateMachine.Replay
open TLS13.ConnectionState.Lemmas
open TLS13.Security.Index

(** {1 Public indices of a connection state} *)

(** The exchange, read off the ClientHello and ServerHello the endpoint
    holds.  [None] before the ServerHello and for the hybrid group. *)
let state_kex_index (st:connection_state) : GTot (option kex_index) =
  let hs = st.cs_model.model_handshake in
  match hs.hs_client_hello, hs.hs_server_hello with
  | Some ch, Some sh ->
    (match server_hello_kex sh with
     | Some (| g, sh_ks |) ->
       (match client_hello_kex ch g with
        | Some ch_ks ->
          Some { kx_group = g; kx_client_share = ch_ks; kx_server_share = sh_ks }
        | None -> None)
     | None -> None)
  | _, _ -> None

(** The index of a first-epoch traffic secret: the exchange plus the
    transcript bytes at the epoch's derivation checkpoint. *)
let state_traffic_index
  (st:connection_state)
  (epoch:traffic_epoch)
  (label:traffic_label)
  : GTot (option traffic_index) =
  match
    state_kex_index st,
    transcript_bytes_for_key_checkpoint (key_checkpoint_for_epoch epoch) st
  with
  | Some k, Some transcript ->
    Some { ti_kex = k; ti_epoch = epoch; ti_label = label; ti_transcript = transcript }
  | _, _ -> None

(** {1 Statements} *)

(** The base secrets of the key schedule are the real values at [dhe]. *)
let base_secrets_at_index (st:connection_state) (dhe:B.bytes) : GTot prop =
  let keys = st.cs_model.model_handshake.hs_keys in
  (match keys.ks_shared_secret with Some s -> (s <: B.bytes) == dhe | None -> False) /\
  keys.ks_early_secret == Some (real_early ()) /\
  keys.ks_handshake_secret == Some (real_handshake dhe) /\
  keys.ks_master_secret == Some (real_master dhe)

(** A present traffic slot holds the real key and IV at its index. *)
let traffic_slot_at_index
  (st:connection_state)
  (dhe:B.bytes)
  (epoch:traffic_epoch)
  (label:traffic_label)
  : GTot prop =
  match
    traffic_material_for_label st.cs_model.model_handshake.hs_keys epoch label
  with
  | None -> True
  | Some m ->
    (match state_traffic_index st epoch label with
     | Some t ->
       (m.traffic_key <: B.bytes) ==
         real_secret dhe
           (IdxAeadKey (negotiated_aead_alg st.cs_model.model_handshake, t)) /\
       (m.traffic_iv <: B.bytes) == real_secret dhe (IdxAeadIV t)
     | None -> False)

let handshake_slots_at_index (st:connection_state) (dhe:B.bytes) : GTot prop =
  traffic_slot_at_index st dhe TrafficHandshake ClientTraffic /\
  traffic_slot_at_index st dhe TrafficHandshake ServerTraffic

let application_slots_at_index (st:connection_state) (dhe:B.bytes) : GTot prop =
  traffic_slot_at_index st dhe TrafficApplication ClientTraffic /\
  traffic_slot_at_index st dhe TrafficApplication ServerTraffic

(** The client's ephemeral private key for the negotiated group. *)
let client_kex_private (st:connection_state) (g:C.dh_group)
  : option C.kex_private =
  match st.cs_model.model_handshake.hs_start with
  | Some start -> start_kex_private start g
  | None -> None

(** The server's ephemeral private key for the negotiated group. *)
let server_kex_private_of (st:connection_state) (g:C.dh_group)
  : option C.kex_private =
  match st.cs_model.model_handshake.hs_server_selection with
  | Some selection -> server_kex_private selection g
  | None -> None

(** Everything a reachable endpoint knows about its secrets, in index form.
    [own_dhe k sk dhe] relates the endpoint's private key to the exchange.
    Application slots are covered while no KeyUpdate has happened (after a
    KeyUpdate the live secret is an iterate of the first-epoch secret; see
    [KeyMaterial.application_traffic_secret_after]). *)
let secrets_at_index
  (own_private:C.dh_group -> option C.kex_private)
  (own_dhe:kex_index -> C.kex_private -> B.bytes -> GTot prop)
  (st:connection_state)
  : GTot prop =
  match state_kex_index st, st.cs_model.model_handshake.hs_keys.ks_shared_secret with
  | Some k, Some dhe ->
    (match own_private k.kx_group with
     | Some sk -> own_dhe k sk dhe
     | None -> False) /\
    base_secrets_at_index st dhe /\
    handshake_slots_at_index st dhe /\
    (connection_state_no_key_update_trace st ==>
      application_slots_at_index st dhe)
  | _, _ -> False

let client_secrets_at_index (st:connection_state) : GTot prop =
  secrets_at_index (client_kex_private st) client_dhe_at st

let server_secrets_at_index (st:connection_state) : GTot prop =
  secrets_at_index (server_kex_private_of st) server_dhe_at st

(** {1 Proofs} *)

let lemma_initial_raw_event_replay (cfg:connection_config)
  : Lemma (connection_state_raw_event_replay_consistent (initial cfg))
=
  assert_norm (connection_state_raw_event_replay_consistent (initial cfg) <==>
    (Seq.equal (initial cfg).cs_wire_log.TLS13.ConnectionLog.raw_sent B.empty /\
     Seq.equal (initial cfg).cs_wire_log.TLS13.ConnectionLog.raw_received B.empty /\
     (initial cfg).cs_model == initial_model cfg))

let lemma_single_step_raw_event_replay (x y:connection_state)
  : Lemma
      (requires
        connection_state_raw_event_replay_consistent x /\
        connection_state_single_step x y)
      (ensures connection_state_raw_event_replay_consistent y)
=
  let aux (delta:connection_delta)
    : Lemma
        (legal_connection_delta x delta y ==>
          connection_state_raw_event_replay_consistent y)
    = FStar.Classical.move_requires
        (lemma_legal_connection_delta_raw_event_replay_consistent x delta) y
  in
  FStar.Classical.forall_intro aux

(** Raw-event replay is a reachability invariant. *)
let lemma_consistent_raw_event_replay (st:connection_state)
  : Lemma
      (requires connection_state_consistent st)
      (ensures connection_state_raw_event_replay_consistent st)
=
  let p = connection_state_raw_event_replay_consistent in
  lemma_initial_raw_event_replay st.cs_model.model_config;
  let aux (x y:connection_state)
    : Lemma (p x /\ connection_state_single_step x y ==> p y)
    = FStar.Classical.move_requires (lemma_single_step_raw_event_replay x) y
  in
  FStar.Classical.forall_intro_2 aux;
  RTC.stable_on_closure connection_state_single_step p ()

(** A slot that matches its expected derived material is at its index, once
    the base secrets are known to be the real ones. *)
let lemma_slot_at_index
  (st:connection_state)
  (dhe:B.bytes)
  (epoch:traffic_epoch)
  (label:traffic_label)
  : Lemma
      (requires
        Some? (state_kex_index st) /\
        base_secrets_at_index st dhe /\
        (Some? (traffic_material_for_label
                  st.cs_model.model_handshake.hs_keys epoch label) ==>
          traffic_material_matches_expected_derived_material
            (traffic_id epoch label) st))
      (ensures traffic_slot_at_index st dhe epoch label)
=
  ()

let lemma_base_secrets_at_index (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        Some? st.cs_model.model_handshake.hs_keys.ks_shared_secret)
      (ensures
        base_secrets_at_index st
          (Some?.v st.cs_model.model_handshake.hs_keys.ks_shared_secret))
=
  lemma_connection_state_consistent_shared_secret_supported_profile_key_schedule_lineage st

let lemma_slots_at_index (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        Some? (state_kex_index st) /\
        Some? st.cs_model.model_handshake.hs_keys.ks_shared_secret)
      (ensures (
        let dhe = Some?.v st.cs_model.model_handshake.hs_keys.ks_shared_secret in
        handshake_slots_at_index st dhe /\
        (connection_state_no_key_update_trace st ==>
          application_slots_at_index st dhe)))
=
  let dhe = Some?.v st.cs_model.model_handshake.hs_keys.ks_shared_secret in
  lemma_base_secrets_at_index st;
  lemma_connection_state_consistent_first_epoch_handshake_traffic_material_slots_match_expected st;
  lemma_slot_at_index st dhe TrafficHandshake ClientTraffic;
  lemma_slot_at_index st dhe TrafficHandshake ServerTraffic;
  introduce connection_state_no_key_update_trace st ==>
    application_slots_at_index st dhe
  with (
    lemma_consistent_raw_event_replay st;
    lemma_connection_state_no_key_update_trace_first_epoch_application_traffic_material_slots_match_expected st;
    lemma_slot_at_index st dhe TrafficApplication ClientTraffic;
    lemma_slot_at_index st dhe TrafficApplication ServerTraffic
  )

(** {1 Key-index lemmas} *)

(** A reachable client that has derived an (EC)DH shared secret holds exactly
    the real secrets at its public indices, and its (EC)DHE output is the DH
    of its own ephemeral key with the server share on the wire. *)
let lemma_client_secrets_at_index (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == ClientEndpoint /\
        Some? st.cs_model.model_handshake.hs_keys.ks_shared_secret /\
        Some? (state_kex_index st))
      (ensures client_secrets_at_index st)
=
  lemma_consistent_shared_secret_stable_client_x25519_projection st;
  lemma_base_secrets_at_index st;
  lemma_slots_at_index st

(** Server mirror.  A failed server is excluded: failure can strike between
    deriving the shared secret and sending the ServerHello, where the
    exchange has no public index yet. *)
let lemma_server_secrets_at_index (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == ServerEndpoint /\
        Some? st.cs_model.model_handshake.hs_keys.ks_shared_secret /\
        st.cs_model.model_control =!= ControlHandshaking HsClientHelloReceived /\
        ~(ControlFailed? st.cs_model.model_control) /\
        Some? (state_kex_index st))
      (ensures server_secrets_at_index st)
=
  lemma_consistent_shared_secret_stable_server_x25519_projection st;
  lemma_base_secrets_at_index st;
  lemma_slots_at_index st
