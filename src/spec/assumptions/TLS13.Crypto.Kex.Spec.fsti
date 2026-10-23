module TLS13.Crypto.Kex.Spec

(**
  The group-generic key exchange of TLS 1.3, in KEM shape.

  (EC)DH is symmetric: both sides publish `g^x` independently and each
  combines its own private key with the peer's public key.  A KEM, and so
  the X25519MLKEM768 hybrid of RFC 10024, is not: the server's share is an
  *encapsulation to the client's share*, and the two sides run different
  functions to reach the shared secret.  This interface is therefore
  direction-explicit:

    client:  csk  --kex_client_public-->  client share
    server:  (ssk, client share) --kex_server_share-->  server share
             (ssk, client share) --kex_server_shared--> shared secret
    client:  (csk, server share) --kex_client_shared--> shared secret

  For the (EC)DH groups every function is, by unfolding, the existing
  symmetric one of [TLS13.Crypto.Spec] (see the `lemma_*_dh` facts), so
  proofs about X25519 and P-256 carry over unchanged.

  Agreement holds under [kex_agreement_ok], which is `True` for the DH
  groups and is ML-KEM's deterministic noise bound for the hybrid (an event
  of probability about 2^-164 that the model does not assume away).
**)

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module H = TLS13.Crypto.Hybrid.Spec

type bytes_of_len (n:nat) = B.bytes_of_len n

let kex_client_private_len (g:C.kex_group) : n:nat{n == 32 \/ n == 96} =
  match g with
  | C.KexX25519 | C.KexP256 -> 32
  | C.KexX25519MLKEM768 -> 96

let kex_server_private_len (g:C.kex_group) : n:nat{n == 32 \/ n == 64} =
  match g with
  | C.KexX25519 | C.KexP256 -> 32
  | C.KexX25519MLKEM768 -> 64

let kex_client_share_len (g:C.kex_group) : n:nat{n == 32 \/ n == 65 \/ n == 1216} =
  match g with
  | C.KexX25519 | C.KexP256 -> C.kex_public_len g
  | C.KexX25519MLKEM768 -> 1216

let kex_server_share_len (g:C.kex_group) : n:nat{n == 32 \/ n == 65 \/ n == 1120} =
  match g with
  | C.KexX25519 | C.KexP256 -> C.kex_public_len g
  | C.KexX25519MLKEM768 -> 1120

let kex_shared_len (g:C.kex_group) : n:nat{n == 32 \/ n == 64} =
  match g with
  | C.KexX25519 | C.KexP256 -> 32
  | C.KexX25519MLKEM768 -> 64

type kex_client_private (g:C.kex_group) = bytes_of_len (kex_client_private_len g)
type kex_server_private (g:C.kex_group) = bytes_of_len (kex_server_private_len g)
type kex_client_share (g:C.kex_group) = bytes_of_len (kex_client_share_len g)
type kex_server_share_t (g:C.kex_group) = bytes_of_len (kex_server_share_len g)
type kex_secret (g:C.kex_group) = bytes_of_len (kex_shared_len g)


let kex_client_public (g:C.kex_group) (csk:B.bytes) : GTot (kex_client_share g) =
  match g with
  | C.KexX25519 | C.KexP256 -> C.kex_public_from_private g csk
  | C.KexX25519MLKEM768 -> H.x25519mlkem768_client_public csk

(** [None] when the server must reject the client's share
    (illegal_parameter).  The (EC)DH groups never reject here: an invalid
    peer point surfaces as a failed [kex_server_shared]. *)
let kex_server_share (g:C.kex_group) (ssk:B.bytes) (client_share:B.bytes)
  : GTot (option (kex_server_share_t g)) =
  match g with
  | C.KexX25519 | C.KexP256 -> Some (C.kex_public_from_private g ssk)
  | C.KexX25519MLKEM768 -> H.x25519mlkem768_server_share ssk client_share

(** The shared secrets are returned at the group-independent
    [C.kex_shared_secret_any], the type the model's key schedule carries;
    [lemma_kex_shared_len] gives the group's exact width. *)
let kex_server_shared (g:C.kex_group) (ssk:B.bytes) (client_share:B.bytes)
  : GTot (option C.kex_shared_secret_any) =
  match g with
  | C.KexX25519 | C.KexP256 -> C.widen_secret (C.kex_shared g ssk client_share)
  | C.KexX25519MLKEM768 -> C.widen_secret (H.x25519mlkem768_server_shared ssk client_share)

let kex_client_shared (g:C.kex_group) (csk:B.bytes) (server_share:B.bytes)
  : GTot (option C.kex_shared_secret_any) =
  match g with
  | C.KexX25519 | C.KexP256 -> C.widen_secret (C.kex_shared g csk server_share)
  | C.KexX25519MLKEM768 -> C.widen_secret (H.x25519mlkem768_client_shared csk server_share)

let lemma_kex_shared_len (g:C.kex_group) (sk:B.bytes) (share:B.bytes)
  : Lemma ((Some? (kex_server_shared g sk share) ==>
            B.length (Some?.v (kex_server_shared g sk share)) == kex_shared_len g) /\
           (Some? (kex_client_shared g sk share) ==>
            B.length (Some?.v (kex_client_shared g sk share)) == kex_shared_len g))
  = ()

let kex_agreement_ok (g:C.kex_group) (csk:B.bytes) (ssk:B.bytes) : prop =
  match g with
  | C.KexX25519 | C.KexP256 -> True
  | C.KexX25519MLKEM768 ->
    H.mlkem768_correct_coins (H.client_d csk) (H.client_z csk) (H.server_m ssk)

(** The DH arms are the symmetric functions of [TLS13.Crypto.Spec]. *)
let lemma_kex_dh (g:C.dh_group) (sk ssk:B.bytes) (share:B.bytes)
  : Lemma (kex_client_share_len g == C.kex_public_len g /\
           kex_server_share_len g == C.kex_public_len g /\
           kex_client_public g sk == C.kex_public_from_private g sk /\
           kex_server_share g ssk share == Some (C.kex_public_from_private g ssk) /\
           kex_server_shared g ssk share == C.widen_secret (C.kex_shared g ssk share) /\
           kex_client_shared g sk share == C.widen_secret (C.kex_shared g sk share) /\
           kex_agreement_ok g sk ssk)
  = ()

(** Key agreement: an honest client's share is accepted, and both sides
    derive the same secret (or both fail, e.g. on an all-zero X25519
    output). *)
val lemma_kex_agreement:
  g:C.kex_group ->
  csk:kex_client_private g ->
  ssk:kex_server_private g ->
  Lemma
    (requires kex_agreement_ok g csk ssk)
    (ensures
      (let cs = kex_client_public g csk in
       Some? (kex_server_share g ssk cs) /\
       kex_client_shared g csk (Some?.v (kex_server_share g ssk cs)) ==
       kex_server_shared g ssk cs))
