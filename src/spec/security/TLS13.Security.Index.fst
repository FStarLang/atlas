module TLS13.Security.Index

(**
  Public indices for the secrets of a 1-RTT (EC)DHE handshake.

  This is the foundation of the computational security argument (see
  SECURITY_DESIGN_AND_IMPL.md).  Every secret a session derives is named by an
  index built only from data the adversary sees on the wire: the two key
  shares and the transcript bytes at the derivation checkpoint.  The real
  value at an index is a function of the index and the (EC)DHE output alone
  ([real_secret]); [TLS13.Security.KeyIndex] proves that every reachable
  connection state holds exactly these values.

  The ideal world replaces [real_secret] at honest indices by independent
  random values.  Traffic secrets are indexed by transcript BYTES rather than
  by the transcript hash on purpose: the hop from one to the other is the
  collision-resistance assumption on SHA-256, and indexing by bytes keeps that
  assumption explicit rather than baking it into the index.
**)

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module K = TLS13.Keys
module KM = TLS13.Spec.StateMachine.KeyMaterial

open TLS13.Spec.StateMachine

(** The (EC)DHE exchange of a session: the group and the two public shares, as
    they appear in the ClientHello and the ServerHello. *)
type kex_index = {
  kx_group: C.dh_group;
  kx_client_share: B.bytes;
  kx_server_share: B.bytes;
}

(** A traffic secret: the exchange it descends from, its epoch and direction
    label, and the transcript bytes it is bound to (ClientHello..ServerHello
    for handshake traffic, ClientHello..server Finished for application
    traffic). *)
type traffic_index = {
  ti_kex: kex_index;
  ti_epoch: traffic_epoch;
  ti_label: traffic_label;
  ti_transcript: B.bytes;
}

type secret_index =
  | IdxShared of kex_index
  | IdxHandshake of kex_index
  | IdxMaster of kex_index
  | IdxTraffic of traffic_index
  | IdxAeadKey of C.aead_alg & traffic_index
  | IdxAeadIV of traffic_index
  | IdxFinishedKey of traffic_index

(** The exchange an index descends from. *)
let secret_index_kex (i:secret_index) : kex_index =
  match i with
  | IdxShared k | IdxHandshake k | IdxMaster k -> k
  | IdxTraffic t | IdxAeadIV t | IdxFinishedKey t -> t.ti_kex
  | IdxAeadKey (_, t) -> t.ti_kex

(** The real key schedule as a function of the (EC)DHE output: the exact
    compositions the state machine performs (no PSK, SHA-256 key schedule).
    [TLS13.Security.KeyIndex] proves the correspondence. *)
let real_early () : GTot C.secret = K.early_secret B.empty

let real_handshake (dhe:B.bytes) : GTot C.secret =
  K.handshake_secret (real_early ()) dhe

let real_master (dhe:B.bytes) : GTot C.secret =
  K.master_secret (real_handshake dhe)

let real_traffic_base (dhe:B.bytes) (epoch:traffic_epoch) : GTot C.secret =
  match epoch with
  | TrafficHandshake -> real_handshake dhe
  | TrafficApplication -> real_master dhe

let real_traffic (dhe:B.bytes) (t:traffic_index) : GTot K.traffic_secret =
  KM.derive_traffic_secret_for_label
    t.ti_epoch t.ti_label (real_traffic_base dhe t.ti_epoch) t.ti_transcript

let real_secret (dhe:B.bytes) (i:secret_index) : GTot B.bytes =
  match i with
  | IdxShared _ -> dhe
  | IdxHandshake _ -> real_handshake dhe
  | IdxMaster _ -> real_master dhe
  | IdxTraffic t -> real_traffic dhe t
  | IdxAeadKey (a, t) -> K.derive_aead_key a (real_traffic dhe t)
  | IdxAeadIV t -> K.derive_aead_iv (real_traffic dhe t)
  | IdxFinishedKey t -> K.finished_key (real_traffic dhe t)

(** [dhe] is the (EC)DHE output of exchange [k] as computed by the endpoint
    holding [sk], whose own share is [own] and whose peer's share is [peer]. *)
let dhe_from_private
  (k:kex_index) (sk:C.kex_private) (own peer:B.bytes) (dhe:B.bytes)
  : GTot prop =
  C.kex_public_from_private k.kx_group sk == own /\
  (match C.widen_secret (C.kex_shared k.kx_group sk peer) with
   | Some s -> (s <: B.bytes) == dhe
   | None -> False)

(** [dhe] as computed by the client, from its ephemeral private key. *)
let client_dhe_at (k:kex_index) (sk:C.kex_private) (dhe:B.bytes) : GTot prop =
  dhe_from_private k sk k.kx_client_share k.kx_server_share dhe

(** [dhe] as computed by the server, from its ephemeral private key. *)
let server_dhe_at (k:kex_index) (sk:C.kex_private) (dhe:B.bytes) : GTot prop =
  dhe_from_private k sk k.kx_server_share k.kx_client_share dhe
