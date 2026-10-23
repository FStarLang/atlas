module TLS13.Crypto.Hybrid.Spec

(**
  ML-KEM-768 (FIPS 203) and the X25519MLKEM768 hybrid key agreement of
  RFC 10024, as pure specifications defined by hacl-pulse's [Spec.MLKEM].

  Unlike the Diffie-Hellman groups in [TLS13.Crypto.Spec], a KEM is
  asymmetric: the server's share is not a function of the server's private
  key alone but an *encapsulation* to the client's share, so the model needs
  three functions where DH needs two.

  RFC 10024 section 4, for X25519MLKEM768 (codepoint 0x11EC):

  - client share (1216 bytes) = ML-KEM-768 encapsulation key (1184)
                                || X25519 public (32)
  - server share (1120 bytes) = ML-KEM-768 ciphertext (1088)
                                || X25519 public (32)
  - shared secret  (64 bytes) = ML-KEM shared secret (32)
                                || X25519 shared secret (32)

  The ML-KEM part comes first in all three (the reverse of RFC 9954's naming
  convention, for historical reasons).

  Private keys are carried as the *seeds* the randomness is drawn as, so they
  are small and fixed-width:

  - client private (96 bytes) = ML-KEM keygen seed d (32) || seed z (32)
                                || X25519 scalar (32)
  - server private (64 bytes) = ML-KEM encapsulation message m (32)
                                || X25519 scalar (32)

  The decapsulation key is a deterministic function of [d] and [z], so the
  client can regenerate it at decapsulation time rather than store 2400 bytes.

  Correctness of ML-KEM is not unconditional: decapsulation recovers the
  encapsulated secret exactly when the accumulated lattice noise is small
  ([Spec.MLKEM.Correctness.noise_ok]), which fails with probability about
  2^-164 for ML-KEM-768 over the choice of seeds.  hacl-pulse proves the
  deterministic statement and leaves the probability bound unproved, so the
  agreement lemma below carries the noise bound as an explicit hypothesis,
  [mlkem768_correct_coins], rather than assuming it.
**)

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module Seq = FStar.Seq

type bytes_of_len (n:nat) = B.bytes_of_len n

(** {2 ML-KEM-768} *)

let mlkem768_ek_len : nat = 1184
let mlkem768_dk_len : nat = 2400
let mlkem768_ct_len : nat = 1088
let mlkem768_ss_len : nat = 32

(** Key generation from the two 32-byte seeds [d] and [z] (FIPS 203
    Algorithm 19, ML-KEM.KeyGen_internal).  Inputs of the wrong length give
    all zeros. *)
val mlkem768_keygen_ek: d:B.bytes -> z:B.bytes -> GTot (bytes_of_len 1184)
val mlkem768_keygen_dk: d:B.bytes -> z:B.bytes -> GTot (bytes_of_len 2400)

(** Encapsulation of the 32-byte message [m] to [ek] (FIPS 203 Algorithm 17,
    ML-KEM.Encaps_internal): the shared secret and the ciphertext. *)
val mlkem768_encaps_ss: ek:B.bytes -> m:B.bytes -> GTot (bytes_of_len 32)
val mlkem768_encaps_ct: ek:B.bytes -> m:B.bytes -> GTot (bytes_of_len 1088)

(** Decapsulation (FIPS 203 Algorithm 18).  Total: a ciphertext that does
    not re-encrypt yields the implicit-rejection secret. *)
val mlkem768_decaps: dk:B.bytes -> ct:B.bytes -> GTot (bytes_of_len 32)

(** The encapsulation-key modulus check of FIPS 203 section 7.2, which
    RFC 10024 section 4.2 requires the server to run on the client's key. *)
val mlkem768_ek_valid: ek:B.bytes -> GTot bool

(** The deterministic side condition under which decapsulation recovers the
    encapsulated secret: the lattice noise determined by [d] (via the client's
    key) and [m] (via the server's encapsulation coins) is small. *)
val mlkem768_correct_coins: d:B.bytes -> z:B.bytes -> m:B.bytes -> GTot prop

val lemma_mlkem768_keygen_ek_valid: d:B.bytes -> z:B.bytes ->
  Lemma (requires B.length d == 32 /\ B.length z == 32)
        (ensures mlkem768_ek_valid (mlkem768_keygen_ek d z))

val lemma_mlkem768_correct: d:B.bytes -> z:B.bytes -> m:B.bytes ->
  Lemma
    (requires B.length d == 32 /\ B.length z == 32 /\ B.length m == 32 /\
              mlkem768_correct_coins d z m)
    (ensures
      mlkem768_decaps (mlkem768_keygen_dk d z)
                      (mlkem768_encaps_ct (mlkem768_keygen_ek d z) m) ==
      mlkem768_encaps_ss (mlkem768_keygen_ek d z) m)

(** {2 X25519MLKEM768} *)

let x25519mlkem768_client_private_len : nat = 96
let x25519mlkem768_server_private_len : nat = 64
let x25519mlkem768_client_share_len : nat = 1216
let x25519mlkem768_server_share_len : nat = 1120
let x25519mlkem768_shared_len : nat = 64

type x25519mlkem768_client_private_t = bytes_of_len 96
type x25519mlkem768_server_private_t = bytes_of_len 64
type x25519mlkem768_client_share_t = bytes_of_len 1216
type x25519mlkem768_server_share_t = bytes_of_len 1120
type x25519mlkem768_shared_secret_t = bytes_of_len 64

(** Field projections of the private keys.  Total over any length (a key of
    the wrong length projects to zeros) so that the functions below can be
    stated over plain [B.bytes], as in [TLS13.Crypto.Spec]. *)
let private_field (sk:B.bytes) (n:nat) (i:nat) (j:nat{i <= j /\ j <= n}) : bytes_of_len (j - i) =
  if B.length sk = n then Seq.slice sk i j else Seq.create (j - i) 0uy
let client_d (sk:B.bytes) : bytes_of_len 32 = private_field sk 96 0 32
let client_z (sk:B.bytes) : bytes_of_len 32 = private_field sk 96 32 64
let client_x (sk:B.bytes) : bytes_of_len 32 = private_field sk 96 64 96
let server_m (sk:B.bytes) : bytes_of_len 32 = private_field sk 64 0 32
let server_x (sk:B.bytes) : bytes_of_len 32 = private_field sk 64 32 64

(** Field projections of the wire shares.  Total over any length so that
    they can be applied to an unvalidated peer share. *)
let share_mlkem (share:B.bytes) (n:nat) : B.bytes =
  if n <= B.length share then Seq.slice share 0 n else B.empty
let share_x25519 (share:B.bytes) (n:nat) : B.bytes =
  if n <= B.length share then Seq.slice share n (B.length share) else B.empty

(** The client's KeyShareEntry.key_exchange. *)
let x25519mlkem768_client_public (sk:B.bytes)
  : GTot x25519mlkem768_client_share_t
  = Seq.append (mlkem768_keygen_ek (client_d sk) (client_z sk))
               (C.x25519_public_from_private (client_x sk))

(** The client share is acceptable to a server: of the right length, and its
    ML-KEM encapsulation key passes the modulus check. *)
let x25519mlkem768_client_share_ok (client_share:B.bytes) : GTot bool =
  B.length client_share = 1216 &&
  mlkem768_ek_valid (share_mlkem client_share 1184)

(** The server's KeyShareEntry.key_exchange: an encapsulation to the
    client's ML-KEM key, then the server's X25519 public.  [None] when the
    client share is rejected (illegal_parameter). *)
let x25519mlkem768_server_share
  (sk:B.bytes)
  (client_share:B.bytes)
  : GTot (option x25519mlkem768_server_share_t)
  = if x25519mlkem768_client_share_ok client_share
    then Some (Seq.append (mlkem768_encaps_ct (share_mlkem client_share 1184) (server_m sk))
                          (C.x25519_public_from_private (server_x sk)))
    else None

(** The server's shared secret.  [None] when the client share is rejected or
    the X25519 part is all-zero (RFC 10024 section 4.3). *)
let x25519mlkem768_server_shared
  (sk:B.bytes)
  (client_share:B.bytes)
  : GTot (option x25519mlkem768_shared_secret_t)
  = if x25519mlkem768_client_share_ok client_share
    then match C.x25519_shared (server_x sk) (share_x25519 client_share 1184) with
         | Some x -> Some (Seq.append (mlkem768_encaps_ss (share_mlkem client_share 1184)
                                                          (server_m sk))
                                      x)
         | None -> None
    else None

(** The client's shared secret.  [None] when the ciphertext has the wrong
    length or the X25519 part is all-zero (illegal_parameter).  ML-KEM
    decapsulation itself cannot fail. *)
let x25519mlkem768_client_shared
  (sk:B.bytes)
  (server_share:B.bytes)
  : GTot (option x25519mlkem768_shared_secret_t)
  = if B.length server_share = 1120
    then match C.x25519_shared (client_x sk) (share_x25519 server_share 1088) with
         | Some x -> Some (Seq.append (mlkem768_decaps (mlkem768_keygen_dk (client_d sk) (client_z sk))
                                                      (share_mlkem server_share 1088))
                                      x)
         | None -> None
    else None

(** Key agreement.  An honest client's share is always accepted, and, when
    the ML-KEM noise is small, both ends compute the same shared secret
    (including agreeing on whether the X25519 part failed). *)
val lemma_x25519mlkem768_agreement:
  csk:x25519mlkem768_client_private_t ->
  ssk:x25519mlkem768_server_private_t ->
  Lemma
    (requires mlkem768_correct_coins (client_d csk) (client_z csk) (server_m ssk))
    (ensures
      (let cs = x25519mlkem768_client_public csk in
       Some? (x25519mlkem768_server_share ssk cs) /\
       x25519mlkem768_client_shared csk (Some?.v (x25519mlkem768_server_share ssk cs)) ==
       x25519mlkem768_server_shared ssk cs))
