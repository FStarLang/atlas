module TLS13.Security.Oracle

(**
  The key oracle of the security games: secrets are looked up by public index
  instead of being computed from private keys.

  A [key_oracle] maps each index to a value.  The real oracle
  ([real_oracle]) computes [Index.real_secret] from a table of (EC)DHE
  outputs.  The ideal oracles of stage 2 differ from it only at honest
  indices, where they return independent random values.  The game runs every
  honest session against an oracle; [lemma_client_coherent] /
  [lemma_server_coherent] say that against the real oracle (and the true
  (EC)DHE table) each reachable session's installed keys are exactly the
  oracle's values -- so the real game is a faithful run of the spec.
**)

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec

open TLS13.Spec.StateMachine
open TLS13.Spec.StateMachine.Correspondence
open TLS13.Spec.StateMachine.Reachability
open TLS13.Security.Index
open TLS13.Security.KeyIndex

(** Secret values by index.  [None] means "not derivable" (e.g. a peer share
    rejected by the group). *)
type key_oracle = secret_index -> GTot (option B.bytes)

(** A table of (EC)DHE outputs by exchange. *)
type dhe_table = kex_index -> GTot (option B.bytes)

let real_oracle (dhe:dhe_table) : key_oracle =
  fun i ->
    match dhe (secret_index_kex i) with
    | Some d -> Some (real_secret d i)
    | None -> None

(** The true (EC)DHE table, from a function naming the private key behind
    each client share.  Honest sessions use fresh ephemeral keys, so this
    function is well defined on honest exchanges; the real game constructs it
    from the honest sessions' randomness. *)
let true_dhe_table (client_private:kex_index -> option C.kex_private) : dhe_table =
  fun k ->
    match client_private k with
    | Some sk ->
      (match C.widen_secret (C.kex_shared k.kx_group sk k.kx_server_share) with
       | Some s -> Some (s <: B.bytes)
       | None -> None)
    | None -> None

(** {1 Coherence of a session with an oracle} *)

let slot_coherent
  (o:key_oracle)
  (st:connection_state)
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
       o (IdxAeadKey (negotiated_aead_alg st.cs_model.model_handshake, t))
         == Some (m.traffic_key <: B.bytes) /\
       o (IdxAeadIV t) == Some (m.traffic_iv <: B.bytes)
     | None -> False)

let as_bytes (#n:nat) (o:option (B.bytes_of_len n)) : option B.bytes =
  match o with
  | Some s -> Some (s <: B.bytes)
  | None -> None

(** Every secret the session holds is the oracle's value at its index. *)
let session_coherent (o:key_oracle) (st:connection_state) : GTot prop =
  match state_kex_index st, st.cs_model.model_handshake.hs_keys.ks_shared_secret with
  | Some k, Some dhe ->
    o (IdxShared k) == Some (dhe <: B.bytes) /\
    o (IdxHandshake k) == as_bytes st.cs_model.model_handshake.hs_keys.ks_handshake_secret /\
    o (IdxMaster k) == as_bytes st.cs_model.model_handshake.hs_keys.ks_master_secret /\
    slot_coherent o st TrafficHandshake ClientTraffic /\
    slot_coherent o st TrafficHandshake ServerTraffic /\
    (connection_state_no_key_update_trace st ==>
      slot_coherent o st TrafficApplication ClientTraffic /\
      slot_coherent o st TrafficApplication ServerTraffic)
  | _, _ -> False

let lemma_secrets_coherent
  (own_private:C.dh_group -> option C.kex_private)
  (own_dhe:kex_index -> C.kex_private -> B.bytes -> GTot prop)
  (dhe:dhe_table)
  (st:connection_state)
  : Lemma
      (requires
        secrets_at_index own_private own_dhe st /\
        (match state_kex_index st, st.cs_model.model_handshake.hs_keys.ks_shared_secret with
         | Some k, Some d -> dhe k == Some (d <: B.bytes)
         | _, _ -> False))
      (ensures session_coherent (real_oracle dhe) st)
=
  ()

(** A reachable client is coherent with the real oracle over any (EC)DHE table
    that agrees with it on its own exchange -- in particular the true table
    when its ephemeral key is the one registered for its share. *)
let lemma_client_coherent (dhe:dhe_table) (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == ClientEndpoint /\
        Some? st.cs_model.model_handshake.hs_keys.ks_shared_secret /\
        (match state_kex_index st with
         | Some k ->
           dhe k == Some (Some?.v st.cs_model.model_handshake.hs_keys.ks_shared_secret <: B.bytes)
         | None -> False))
      (ensures session_coherent (real_oracle dhe) st)
=
  lemma_client_secrets_at_index st;
  lemma_secrets_coherent (client_kex_private st) client_dhe_at dhe st

(** The true table agrees with a reachable client on its exchange, provided
    it registers the client's own ephemeral key for the client's share. *)
let lemma_true_dhe_table_client
  (client_private:kex_index -> option C.kex_private)
  (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == ClientEndpoint /\
        Some? st.cs_model.model_handshake.hs_keys.ks_shared_secret /\
        (match state_kex_index st with
         | Some k -> client_private k == client_kex_private st k.kx_group
         | None -> False))
      (ensures
        (match state_kex_index st with
         | Some k ->
           true_dhe_table client_private k ==
             Some (Some?.v st.cs_model.model_handshake.hs_keys.ks_shared_secret <: B.bytes)
         | None -> False))
=
  lemma_client_secrets_at_index st

let lemma_server_coherent (dhe:dhe_table) (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == ServerEndpoint /\
        Some? st.cs_model.model_handshake.hs_keys.ks_shared_secret /\
        st.cs_model.model_control =!= ControlHandshaking HsClientHelloReceived /\
        ~(ControlFailed? st.cs_model.model_control) /\
        (match state_kex_index st with
         | Some k ->
           dhe k == Some (Some?.v st.cs_model.model_handshake.hs_keys.ks_shared_secret <: B.bytes)
         | None -> False))
      (ensures session_coherent (real_oracle dhe) st)
=
  lemma_server_secrets_at_index st;
  lemma_secrets_coherent (server_kex_private_of st) server_dhe_at dhe st
