module TLS13.Crypto.Spec

module B = TLS13.Bytes
module T = TLS13.Types
module Seq = FStar.Seq
module U8 = FStar.UInt8

type bytes_of_len (n:nat) = B.bytes_of_len n

type digest32 = bytes_of_len 32
type secret = bytes_of_len 32

(**
  The two AEAD algorithms ATLAS supports, corresponding to the two cipher
  suites it offers.  Both use a 12-byte nonce and a 16-byte tag, so record
  framing is independent of the choice; only the key length differs.
**)
type aead_alg =
  | AEAD_AES128_GCM
  | AEAD_CHACHA20_POLY1305

let aead_key_len (a:aead_alg) : n:nat{n == 16 \/ n == 32} =
  match a with
  | AEAD_AES128_GCM -> 16
  | AEAD_CHACHA20_POLY1305 -> 32

(**
  The negotiated AEAD algorithm is carried as an explicit tag: it lives on the
  record-layer `direction_state` and on `traffic_key_material`, both threaded
  from the accepted ServerHello's cipher suite.  It is deliberately NOT
  recovered from `B.length key` — key lengths collide across algorithms
  (AES-256-GCM and ChaCha20-Poly1305 are both 32 bytes), so length inference is
  neither sound in general nor an honest description of what was negotiated.
**)

type aead_key (a:aead_alg) = bytes_of_len (aead_key_len a)
type aead_key_any = k:B.bytes{B.length k == 16 \/ B.length k == 32}

(**
  Runtime buffers holding a traffic key are always 32 bytes wide, so that the
  buffer layout does not depend on the negotiated suite.  A 16-byte AES key is
  stored zero-padded to 32 bytes; the logical key is the `aead_key_len`-byte
  prefix.  `pad_key_32` is the spec-level image of that storage convention, so
  representation predicates can pin the full 32-byte buffer contents while the
  model keeps the exact-length key.
**)
let pad_key_32 (k:aead_key_any) : bytes_of_len 32 =
  Seq.append k (Seq.create (32 - B.length k) 0uy)

(** Total inverse of `pad_key_32`: recovers the logical key from a padded
    32-byte buffer.  Total (rather than refined) so it can appear in
    postconditions, where `requires` clauses are not in scope. **)
let unpad_key_32 (key:B.bytes) (key_len:nat) : B.bytes =
  if key_len < B.length key then Seq.slice key 0 key_len else key

(** At the full buffer width the padding is empty, so unpadding is the
    identity.  Stated with a pattern because `requires` clauses of a Pulse
    signature are not in scope for its `ensures`, so call sites must recover
    this from the buffer length alone. **)
let lemma_unpad_key_32_full (key:B.bytes) (key_len:nat)
  : Lemma (requires key_len >= B.length key)
          (ensures unpad_key_32 key key_len == key)
          [SMTPat (unpad_key_32 key key_len)]
  = ()

let lemma_pad_key_32_prefix (k:aead_key_any)
  : Lemma (ensures Seq.equal (Seq.slice (pad_key_32 k) 0 (B.length k)) k)
          [SMTPat (pad_key_32 k)]
  = ()

(** Round trip: unpadding a padded key at its own length recovers it. **)
let lemma_unpad_pad_key_32 (k:aead_key_any)
  : Lemma (ensures unpad_key_32 (pad_key_32 k) (B.length k) == k)
  = if B.length k < 32
    then Seq.lemma_eq_intro (Seq.slice (pad_key_32 k) 0 (B.length k)) k
    else Seq.lemma_eq_intro (pad_key_32 k) k

(** The logical AEAD key held by a 32-byte padded traffic-key buffer, given the
    negotiated algorithm.  Every layer that stores a padded key buffer alongside
    its algorithm projects it with this. **)
let logical_key (a:aead_alg) (k:B.bytes) : B.bytes =
  unpad_key_32 k (aead_key_len a)

let lemma_logical_key_length (a:aead_alg) (k:B.bytes)
  : Lemma (requires B.length k == 32)
          (ensures B.length (logical_key a k) == aead_key_len a)
          [SMTPat (logical_key a k)]
  = ()

(** `pad_key_32` is injective: the key length is recoverable, so no two
    distinct keys share a padded image. **)
let lemma_pad_key_32_injective (k1 k2:aead_key_any)
  : Lemma (requires B.length k1 == B.length k2 /\
                    Seq.equal (pad_key_32 k1) (pad_key_32 k2))
          (ensures Seq.equal k1 k2)
  = assert (Seq.equal k1 (Seq.slice (pad_key_32 k1) 0 (B.length k1)));
    assert (Seq.equal k2 (Seq.slice (pad_key_32 k2) 0 (B.length k2)))
type aead_nonce = bytes_of_len 12
type x25519_private = bytes_of_len 32
type x25519_public = bytes_of_len 32
type x25519_shared_secret = secret
type public_key = B.bytes
type signature = B.bytes

val sha256: msg:B.bytes -> GTot digest32

val hmac_sha256: key:B.bytes -> msg:B.bytes -> GTot digest32

val hkdf_extract: salt:B.bytes -> ikm:B.bytes -> GTot secret

val x25519_public_from_private:
  sk:B.bytes ->
  GTot x25519_public

val x25519_shared:
  sk:B.bytes ->
  pk:B.bytes ->
  GTot (option x25519_shared_secret)

val lemma_x25519_shared_agreement:
  client_sk:x25519_private ->
  server_sk:x25519_private ->
  client_pub:x25519_public ->
  server_pub:x25519_public ->
  Lemma
    (requires
      x25519_public_from_private client_sk == client_pub /\
      x25519_public_from_private server_sk == server_pub)
    (ensures
      x25519_shared client_sk server_pub ==
      x25519_shared server_sk client_pub)

(**
  secp256r1 (NIST P-256).  The private key is 32 bytes as for X25519, but the
  public value is the 65-byte uncompressed SEC1 point `0x04 || X || Y` that TLS
  puts in a `KeyShareEntry`.  The shared secret is the 32-byte X coordinate of
  the shared point (RFC 8446 section 7.4.2), so it has the same type as the
  X25519 one and the key schedule above it is unchanged.

  `p256_shared` is partial: unlike X25519 it can fail, because a peer's point
  must lie on the curve and P-256 has no all-zero-output convention to fall
  back on.
**)
type p256_private = bytes_of_len 32
type p256_public = bytes_of_len 65

val p256_public_from_private:
  sk:B.bytes ->
  GTot p256_public

val p256_shared:
  sk:B.bytes ->
  pk:B.bytes ->
  GTot (option x25519_shared_secret)

val lemma_p256_shared_agreement:
  client_sk:p256_private ->
  server_sk:p256_private ->
  client_pub:p256_public ->
  server_pub:p256_public ->
  Lemma
    (requires
      p256_public_from_private client_sk == client_pub /\
      p256_public_from_private server_sk == server_pub)
    (ensures
      p256_shared client_sk server_pub ==
      p256_shared server_sk client_pub)

(**
  The negotiated key-exchange group.  Like the AEAD algorithm, this is carried
  as an explicit tag and never recovered from a share's length: `kex_public_len`
  happens to be injective today, but the group is what the peer actually named
  in its `KeyShareEntry` and there is no reason to launder it through a size.
**)
type kex_group =
  | KexX25519
  | KexP256
  | KexX25519MLKEM768

(**
  The (EC)DH groups: a single private key, a public key that does not depend
  on the peer, and a symmetric `kex_shared`.  The X25519MLKEM768 hybrid (RFC
  10024) is not of this shape -- the server's share is an encapsulation to
  the client's -- and its direction-explicit interface, together with a
  group-generic one, lives in [TLS13.Crypto.Kex.Spec].
**)
let is_dh_group (g:kex_group) : bool =
  match g with
  | KexX25519 | KexP256 -> true
  | KexX25519MLKEM768 -> false

type dh_group = g:kex_group{is_dh_group g}

let kex_public_len (g:dh_group) : n:nat{n == 32 \/ n == 65} =
  match g with
  | KexX25519 -> 32
  | KexP256 -> 65

type kex_private = bytes_of_len 32
type kex_public (g:dh_group) = bytes_of_len (kex_public_len g)
type kex_shared_secret = x25519_shared_secret

(**
  The `(EC)DHE` input to HKDF-Extract for any group: 32 bytes for X25519 and
  P-256, 64 for the X25519MLKEM768 hybrid (RFC 10024).  The key schedule is
  defined over arbitrary bytes, so the model carries the secret at this type
  and the negotiated group decides its width.
**)
type kex_shared_secret_any = s:B.bytes{B.length s == 32 \/ B.length s == 64}

(** F* has no subtyping under [option], so a group-specific result is widened
    explicitly before it is compared with a model-level secret. *)
let widen_secret (#n:nat{n == 32 \/ n == 64}) (o:option (bytes_of_len n))
  : option kex_shared_secret_any =
  match o with
  | Some s -> Some s
  | None -> None

let lemma_widen_secret (#n:nat{n == 32 \/ n == 64}) (o:option (bytes_of_len n))
  : Lemma (Some? (widen_secret o) == Some? o /\
           (Some? o ==> (Some?.v (widen_secret o) <: B.bytes) == (Some?.v o <: B.bytes)))
          [SMTPat (widen_secret o)]
  = ()

let kex_public_from_private (g:dh_group) (sk:B.bytes) : GTot (kex_public g) =
  match g with
  | KexX25519 -> x25519_public_from_private sk
  | KexP256 -> p256_public_from_private sk

let kex_shared (g:dh_group) (sk:B.bytes) (pk:B.bytes) : GTot (option kex_shared_secret) =
  match g with
  | KexX25519 -> x25519_shared sk pk
  | KexP256 -> p256_shared sk pk

(**
  Runtime buffers holding a peer key share are always 65 bytes wide -- the
  widest group -- so that the buffer layout does not depend on the negotiated
  group, exactly as `pad_key_32` does for AEAD keys.  A 32-byte X25519 share is
  stored zero-padded; the logical share is the `kex_public_len`-byte prefix, and
  which prefix that is comes from the explicit group tag, never from the buffer.
**)
type kex_public_any = k:B.bytes{B.length k == 32 \/ B.length k == 65}

let pad_share_65 (k:kex_public_any) : bytes_of_len 65 =
  Seq.append k (Seq.create (65 - B.length k) 0uy)

(** Total inverse of `pad_share_65`, in the same style as `unpad_key_32`. **)
let unpad_share_65 (share:B.bytes) (share_len:nat) : B.bytes =
  if share_len < B.length share then Seq.slice share 0 share_len else share

let lemma_unpad_share_65 (k:kex_public_any)
  : Lemma (unpad_share_65 (pad_share_65 k) (B.length k) == k)
          [SMTPat (unpad_share_65 (pad_share_65 k) (B.length k))]
  = assert (Seq.equal (Seq.slice (pad_share_65 k) 0 (B.length k)) k)

(**
  A 65-byte buffer is a *padded* share of width [share_len] when it is exactly
  [pad_share_65] of its own [share_len]-byte prefix -- i.e. the bytes past the
  logical share are zero.  This is the shape the ServerHello representation
  stores, and the shape [TLS13.KEX.kex_public_from_private_runtime] produces
  when handed a zeroed buffer.
**)
let padded_share_65 (share:B.bytes) (share_len:nat) : prop =
  B.length share == 65 /\
  (share_len == 32 \/ share_len == 65) /\
  Seq.equal share (pad_share_65 (unpad_share_65 share share_len))

let lemma_pad_share_65_injective (k1 k2:kex_public_any)
  : Lemma (requires Seq.equal (pad_share_65 k1) (pad_share_65 k2) /\
                    B.length k1 == B.length k2)
          (ensures Seq.equal k1 k2)
  = assert (Seq.equal k1 (Seq.slice (pad_share_65 k1) 0 (B.length k1)));
    assert (Seq.equal k2 (Seq.slice (pad_share_65 k2) 0 (B.length k2)))

let lemma_kex_shared_agreement
  (g:dh_group)
  (client_sk server_sk:kex_private)
  (client_pub server_pub:kex_public g)
  : Lemma
      (requires
        kex_public_from_private g client_sk == client_pub /\
        kex_public_from_private g server_sk == server_pub)
      (ensures
        kex_shared g client_sk server_pub ==
        kex_shared g server_sk client_pub)
  = match g with
    | KexX25519 -> lemma_x25519_shared_agreement client_sk server_sk client_pub server_pub
    | KexP256 -> lemma_p256_shared_agreement client_sk server_sk client_pub server_pub

let nonce_byte (seq:nat) (divisor:pos) : U8.t =
  U8.uint_to_t ((seq / divisor) % 256)

let byte_at (bytes:B.bytes) (i:nat) : GTot U8.t =
  if i < B.length bytes then Seq.index bytes i else 0uy

let update_byte
  (bytes:B.bytes)
  (i:nat)
  (value:U8.t)
  : GTot B.bytes =
  if i < B.length bytes then Seq.upd bytes i value else bytes

let hkdf_label_info_length
  (label:B.bytes)
  (context:B.bytes)
  : nat =
  10 + B.length label + B.length context

let copy_bytes_into
  (dst:B.bytes)
  (offset:nat)
  (src:B.bytes)
  : GTot (bytes_of_len (B.length dst)) =
  if offset + B.length src <= B.length dst
  then
    B.append
      (Seq.slice dst 0 offset)
      (B.append
        src
        (Seq.slice dst (offset + B.length src) (B.length dst)))
  else dst

(** Fixed-capacity representation of RFC 8446 HkdfLabel. Only the
    [hkdf_label_info_length label context] prefix is passed to HKDF-Expand. *)
[@@ "opaque_to_smt"]
let hkdf_label_info_buffer
  (label:B.bytes)
  (context:B.bytes)
  (len:nat)
  : GTot (bytes_of_len 520) =
  let info0 = B.zeros 520 in
  let info1 = update_byte info0 0 (U8.uint_to_t ((len / 256) % 256)) in
  let info2 = update_byte info1 1 (U8.uint_to_t (len % 256)) in
  let info3 =
    update_byte info2 2 (U8.uint_to_t ((6 + B.length label) % 256)) in
  let info4 = update_byte info3 3 0x74uy in
  let info5 = update_byte info4 4 0x6cuy in
  let info6 = update_byte info5 5 0x73uy in
  let info7 = update_byte info6 6 0x31uy in
  let info8 = update_byte info7 7 0x33uy in
  let info9 = update_byte info8 8 0x20uy in
  let info10 = copy_bytes_into info9 9 label in
  let info11 =
    update_byte info10 (9 + B.length label)
      (U8.uint_to_t (B.length context % 256)) in
  copy_bytes_into info11 (10 + B.length label) context

val hkdf_expand_label:
  secret:B.bytes ->
  label:B.bytes ->
  context:B.bytes ->
  len:nat ->
  GTot (bytes_of_len len)

[@@ "opaque_to_smt"]
let record_nonce_from_bytes
  (static_iv:B.bytes)
  (seq4 seq5 seq6 seq7 seq8 seq9 seq10 seq11:U8.t)
  : GTot (bytes_of_len (B.length static_iv)) =
  let nonce4 =
    update_byte static_iv 4 (U8.logxor (byte_at static_iv 4) seq4) in
  let nonce5 =
    update_byte nonce4 5 (U8.logxor (byte_at nonce4 5) seq5) in
  let nonce6 =
    update_byte nonce5 6 (U8.logxor (byte_at nonce5 6) seq6) in
  let nonce7 =
    update_byte nonce6 7 (U8.logxor (byte_at nonce6 7) seq7) in
  let nonce8 =
    update_byte nonce7 8 (U8.logxor (byte_at nonce7 8) seq8) in
  let nonce9 =
    update_byte nonce8 9 (U8.logxor (byte_at nonce8 9) seq9) in
  let nonce10 =
    update_byte nonce9 10 (U8.logxor (byte_at nonce9 10) seq10) in
  update_byte nonce10 11 (U8.logxor (byte_at nonce10 11) seq11)

[@@ "opaque_to_smt"]
let tls13_record_nonce
  (static_iv:B.bytes)
  (seq:nat)
  : GTot (bytes_of_len (B.length static_iv)) =
  record_nonce_from_bytes static_iv
    (nonce_byte seq 72057594037927936)
    (nonce_byte seq 281474976710656)
    (nonce_byte seq 1099511627776)
    (nonce_byte seq 4294967296)
    (nonce_byte seq 16777216)
    (nonce_byte seq 65536)
    (nonce_byte seq 256)
    (nonce_byte seq 1)

(**
  The largest plaintext and additional data the AEAD model is defined on.
  Beyond it [aead_seal] and [aead_open] are total but meaningless (all-zero
  output and [None] respectively); a TLS record is far smaller (RFC 8446
  section 5.2 bounds a TLSCiphertext fragment by 2^14 + 256 bytes).
**)
let aead_max_len : nat = 65280

val aead_seal:
  alg:aead_alg ->
  key:B.bytes ->
  nonce:B.bytes ->
  aad:B.bytes ->
  plaintext:B.bytes ->
  GTot (bytes_of_len (B.length plaintext + 16))

val aead_open:
  alg:aead_alg ->
  key:B.bytes ->
  nonce:B.bytes ->
  aad:B.bytes ->
  ciphertext:B.bytes ->
  GTot (option (plaintext:B.bytes{B.length plaintext + 16 == B.length ciphertext}))

(**
  AEAD correctness for honest encryption/decryption with the same algorithm,
  key, nonce, and additional authenticated data, for inputs within
  [aead_max_len].  Proved from hacl-pulse's ChaCha20-Poly1305 and AES-GCM
  specifications.

  Both supported algorithms have a 16-byte tag, so the ciphertext length
  relation above is algorithm-independent and the record framing proofs are
  unaffected by the choice of AEAD.
**)
val lemma_aead_open_seal:
  alg:aead_alg ->
  key:B.bytes ->
  nonce:B.bytes ->
  aad:B.bytes ->
  plaintext:B.bytes ->
  Lemma
    (requires B.length plaintext <= aead_max_len /\ B.length aad <= aead_max_len)
    (ensures aead_open
      alg
      key
      nonce
      aad
      (aead_seal alg key nonce aad plaintext) ==
      Some plaintext)

(** {2 Signature verification}

  A peer's [public_key] is its leaf certificate (DER).  Verification is
  hacl-pulse's: [verify_signature] is defined in the implementation of this
  module from hacl-pulse's RSASSA-PSS and P-256 ECDSA specifications, applied
  to the key [certificate_raw_public_key] reads out of the certificate's
  SubjectPublicKeyInfo. *)

(** A SubjectPublicKeyInfo in the raw form the hacl-pulse verifiers consume:
    an [rsaEncryption] key as its big-endian modulus and public exponent, or
    a P-256 or P-384 key as its 64- or 96-byte affine point [x || y]. *)
type raw_public_key =
  | RawRsa : modulus:B.bytes -> exponent:B.bytes -> raw_public_key
  | RawP256 : point:B.bytes -> raw_public_key
  | RawP384 : point:B.bytes -> raw_public_key

(** {3 Certificate public keys}

    The key is read from the certificate by DER structure alone:
    [Certificate ::= SEQUENCE { tbsCertificate, ... }] spanning the whole
    input, and [tbsCertificate ::= SEQUENCE { [0] version OPTIONAL,
    serialNumber, signature, issuer, validity, subject,
    subjectPublicKeyInfo, ... }] (RFC 5280 4.1).  Tags are single-byte;
    lengths are definite and minimally encoded, at most two length bytes
    (certificates here are far below 64 KiB). *)

(** The content range of the DER TLV with tag [tag] at [pos], if it lies
    within [limit]. *)
let der_tlv (c:B.bytes) (tag:U8.t) (pos limit:nat)
  : option (r:(nat & nat){
      pos + 2 <= fst r /\ fst r <= snd r /\ snd r <= limit /\ limit <= B.length c}) =
  if limit > B.length c || pos + 2 > limit then None
  else if Seq.index c pos <> tag then None
  else
    let l0 = U8.v (Seq.index c (pos + 1)) in
    if l0 < 0x80 then
      (if pos + 2 + l0 <= limit then Some (pos + 2, pos + 2 + l0) else None)
    else if l0 = 0x81 then
      (if pos + 3 > limit then None
       else
         let l = U8.v (Seq.index c (pos + 2)) in
         if l >= 0x80 && pos + 3 + l <= limit then Some (pos + 3, pos + 3 + l) else None)
    else if l0 = 0x82 then
      (if pos + 4 > limit then None
       else
         let l = 256 * U8.v (Seq.index c (pos + 2)) + U8.v (Seq.index c (pos + 3)) in
         if l >= 0x100 && pos + 4 + l <= limit then Some (pos + 4, pos + 4 + l) else None)
    else None

(** The end of the DER TLV with tag [tag] at [pos], if any. *)
let der_skip (c:B.bytes) (tag:U8.t) (pos:option nat) (limit:nat) : option nat =
  match pos with
  | None -> None
  | Some p ->
    (match der_tlv c tag p limit with
     | Some r -> Some (snd r)
     | None -> None)

(** The content range of a certificate's [subjectPublicKeyInfo]. *)
let certificate_spki (c:B.bytes)
  : option (r:(nat & nat){fst r <= snd r /\ snd r <= B.length c}) =
  match der_tlv c 0x30uy 0 (B.length c) with
  | None -> None
  | Some (cs, ce) ->
    if ce <> B.length c then None
    else
      match der_tlv c 0x30uy cs ce with
      | None -> None
      | Some (ts, te) ->
        let version_end =
          (match der_tlv c 0xA0uy ts te with
           | Some r -> snd r
           | None -> ts) in
        let p = der_skip c 0x02uy (Some version_end) te in  (* serialNumber *)
        let p = der_skip c 0x30uy p te in  (* signature *)
        let p = der_skip c 0x30uy p te in  (* issuer *)
        let p = der_skip c 0x30uy p te in  (* validity *)
        let p = der_skip c 0x30uy p te in  (* subject *)
        match p with
        | None -> None
        | Some p ->
          (match der_tlv c 0x30uy p te with
           | Some r -> Some r
           | None -> None)

(** Where the magnitude of a non-negative, minimally encoded DER INTEGER with
    content [s, e) starts: past its sign byte, if it has one. *)
let der_uint_start (c:B.bytes) (s e:nat) : option (n:nat{s <= n /\ n < e /\ e <= B.length c}) =
  if s >= e || e > B.length c then None
  else if U8.v (Seq.index c s) >= 0x80 then None
  else if U8.v (Seq.index c s) = 0 && s + 1 < e then
    (if U8.v (Seq.index c (s + 1)) < 0x80 then None else Some (s + 1))
  else Some s

(** [AlgorithmIdentifier] content [s, e) is [rsaEncryption] (1.2.840.113549.1.1.1)
    with NULL parameters (RFC 3279 2.3.1). *)
let rsa_encryption_algorithm (c:B.bytes) (s e:nat) : bool =
  e = s + 13 && e <= B.length c &&
  Seq.index c s = 0x06uy && Seq.index c (s + 1) = 0x09uy &&
  Seq.index c (s + 2) = 0x2Auy && Seq.index c (s + 3) = 0x86uy &&
  Seq.index c (s + 4) = 0x48uy && Seq.index c (s + 5) = 0x86uy &&
  Seq.index c (s + 6) = 0xF7uy && Seq.index c (s + 7) = 0x0Duy &&
  Seq.index c (s + 8) = 0x01uy && Seq.index c (s + 9) = 0x01uy &&
  Seq.index c (s + 10) = 0x01uy && Seq.index c (s + 11) = 0x05uy &&
  Seq.index c (s + 12) = 0x00uy

(** [AlgorithmIdentifier] content [s, e) is [id-ecPublicKey] (1.2.840.10045.2.1)
    on the named curve [prime256v1] (1.2.840.10045.3.1.7) (RFC 5480 2.1.1). *)
let p256_algorithm (c:B.bytes) (s e:nat) : bool =
  e = s + 19 && e <= B.length c &&
  Seq.index c s = 0x06uy && Seq.index c (s + 1) = 0x07uy &&
  Seq.index c (s + 2) = 0x2Auy && Seq.index c (s + 3) = 0x86uy &&
  Seq.index c (s + 4) = 0x48uy && Seq.index c (s + 5) = 0xCEuy &&
  Seq.index c (s + 6) = 0x3Duy && Seq.index c (s + 7) = 0x02uy &&
  Seq.index c (s + 8) = 0x01uy && Seq.index c (s + 9) = 0x06uy &&
  Seq.index c (s + 10) = 0x08uy && Seq.index c (s + 11) = 0x2Auy &&
  Seq.index c (s + 12) = 0x86uy && Seq.index c (s + 13) = 0x48uy &&
  Seq.index c (s + 14) = 0xCEuy && Seq.index c (s + 15) = 0x3Duy &&
  Seq.index c (s + 16) = 0x03uy && Seq.index c (s + 17) = 0x01uy &&
  Seq.index c (s + 18) = 0x07uy

(** [AlgorithmIdentifier] content [s, e) is [id-ecPublicKey] (1.2.840.10045.2.1)
    on the named curve [secp384r1] (1.3.132.0.34) (RFC 5480 2.1.1). *)
let p384_algorithm (c:B.bytes) (s e:nat) : bool =
  e = s + 16 && e <= B.length c &&
  Seq.index c s = 0x06uy && Seq.index c (s + 1) = 0x07uy &&
  Seq.index c (s + 2) = 0x2Auy && Seq.index c (s + 3) = 0x86uy &&
  Seq.index c (s + 4) = 0x48uy && Seq.index c (s + 5) = 0xCEuy &&
  Seq.index c (s + 6) = 0x3Duy && Seq.index c (s + 7) = 0x02uy &&
  Seq.index c (s + 8) = 0x01uy && Seq.index c (s + 9) = 0x06uy &&
  Seq.index c (s + 10) = 0x05uy && Seq.index c (s + 11) = 0x2Buy &&
  Seq.index c (s + 12) = 0x81uy && Seq.index c (s + 13) = 0x04uy &&
  Seq.index c (s + 14) = 0x00uy && Seq.index c (s + 15) = 0x22uy

(** The raw key in [SubjectPublicKeyInfo ::= SEQUENCE { algorithm, BIT STRING }]
    content [ss, se): for [rsaEncryption], the magnitudes of the modulus and
    exponent of [RSAPublicKey ::= SEQUENCE { INTEGER, INTEGER }]; for P-256
    and P-384, the [x || y] of an uncompressed point (SEC 1 2.3.3).  The BIT STRING must
    have no unused bits. *)
let spki_raw_public_key (c:B.bytes) (ss se:nat) : option raw_public_key =
  match der_tlv c 0x30uy ss se with
  | None -> None
  | Some (a_s, a_e) ->
    match der_tlv c 0x03uy a_e se with
    | None -> None
    | Some (bs, be) ->
      if be <> se || bs >= be || Seq.index c bs <> 0x00uy then None
      else if rsa_encryption_algorithm c a_s a_e then
        (match der_tlv c 0x30uy (bs + 1) be with
         | None -> None
         | Some (rs, re) ->
           if re <> be then None
           else
             match der_tlv c 0x02uy rs re with
             | None -> None
             | Some (ns, ne) ->
               match der_tlv c 0x02uy ne re with
               | None -> None
               | Some (es, ee) ->
                 if ee <> re then None
                 else
                   match der_uint_start c ns ne, der_uint_start c es ee with
                   | Some n0, Some e0 ->
                     Some (RawRsa (Seq.slice c n0 ne) (Seq.slice c e0 ee))
                   | _, _ -> None)
      else if p256_algorithm c a_s a_e then
        (if be = bs + 66 && Seq.index c (bs + 1) = 0x04uy
         then Some (RawP256 (Seq.slice c (bs + 2) be))
         else None)
      else if p384_algorithm c a_s a_e then
        (if be = bs + 98 && Seq.index c (bs + 1) = 0x04uy
         then Some (RawP384 (Seq.slice c (bs + 2) be))
         else None)
      else None

(** The [rsaEncryption], P-256 or P-384 public key a DER certificate carries. *)
let certificate_raw_public_key (certificate:public_key) : option raw_public_key =
  match certificate_spki certificate with
  | Some (ss, se) -> spki_raw_public_key certificate ss se
  | None -> None

(** {3 ECDSA signatures}

    TLS carries an ECDSA signature as the DER encoding of
    [Ecdsa-Sig-Value ::= SEQUENCE { r INTEGER, s INTEGER }] (RFC 8446 4.2.3,
    RFC 3279 2.2.3).  Decoding is strict DER: one definite short-form
    SEQUENCE spanning the whole input, two minimally encoded non-negative
    INTEGERs, nothing else.  With [w]-byte scalars every such encoding is at
    most [2w + 8] bytes (72 for P-256, 104 for P-384), so long-form lengths
    never occur. *)

(** Scalar widths: 32 bytes for P-256, 48 for P-384. *)
type ecdsa_width = w:nat{w == 32 \/ w == 48}

(** The [w]-byte big-endian value of the contents of a DER INTEGER, if it is
    minimal, non-negative, and below [2^(8w)]. *)
let der_integer_n (w:ecdsa_width) (v:B.bytes) : option (bytes_of_len w) =
  let l = B.length v in
  if l = 0 || l > w + 1 then None
  else if U8.v (Seq.index v 0) >= 0x80 then None
  else if l > 1 && U8.v (Seq.index v 0) = 0 && U8.v (Seq.index v 1) < 0x80 then None
  else if l = w + 1 then Some (Seq.slice v 1 (w + 1))
  else Some (Seq.append (Seq.create (w - l) 0uy) v)

let ecdsa_signature_der_decode_n (w:ecdsa_width) (sg:B.bytes)
  : option (bytes_of_len w & bytes_of_len w) =
  let n = B.length sg in
  if n < 8 || n > 2 * w + 8 then None
  else if U8.v (Seq.index sg 0) <> 0x30 || U8.v (Seq.index sg 1) <> n - 2 then None
  else if U8.v (Seq.index sg 2) <> 0x02 then None
  else
    let rl = U8.v (Seq.index sg 3) in
    if 6 + rl > n then None
    else if U8.v (Seq.index sg (4 + rl)) <> 0x02 then None
    else
      let sl = U8.v (Seq.index sg (5 + rl)) in
      if 6 + rl + sl <> n then None
      else
        match der_integer_n w (Seq.slice sg 4 (4 + rl)),
              der_integer_n w (Seq.slice sg (6 + rl) n) with
        | Some r, Some s -> Some (r, s)
        | _, _ -> None

let ecdsa_signature_der_decode (sg:B.bytes) : option (bytes_of_len 32 & bytes_of_len 32) =
  ecdsa_signature_der_decode_n 32 sg

(** {3 RSA moduli}

    A modulus is accepted as a minimal big-endian string (no leading zero
    byte) of 128 to 1024 bytes, i.e. roughly 1024- to 8192-bit RSA; its bit
    length is what RSASSA-PSS calls [modBits]. *)

let byte_bit_length (x:U8.t) : n:nat{n <= 8} =
  let v = U8.v x in
  if v >= 128 then 8 else if v >= 64 then 7 else if v >= 32 then 6
  else if v >= 16 then 5 else if v >= 8 then 4 else if v >= 4 then 3
  else if v >= 2 then 2 else if v >= 1 then 1 else 0

let rsa_max_modulus_bytes : nat = 1024
let rsa_min_modulus_bytes : nat = 128

let rsa_modulus_ok (n:B.bytes) : bool =
  rsa_min_modulus_bytes <= B.length n &&
  B.length n <= rsa_max_modulus_bytes &&
  U8.v (Seq.index n 0) <> 0

let rsa_mod_bits (n:B.bytes{rsa_modulus_ok n}) : nat =
  8 * (B.length n - 1) + byte_bit_length (Seq.index n 0)

(** RSASSA-PSS-VERIFY (RFC 8017 8.1.2) with SHA-256, MGF1-SHA-256 and a
    32-byte salt -- [rsa_pss_rsae_sha256] (RFC 8446 4.2.3) -- by an
    [rsaEncryption] key [(modulus, exponent)]. *)
val rsa_pss_rsae_sha256_verify:
  modulus:B.bytes ->
  exponent:B.bytes ->
  message:B.bytes ->
  signature:signature ->
  GTot bool

(** The hash of an RSASSA-PKCS1-v1_5 certificate signature. *)
type pkcs1_hash =
  | Pkcs1Sha256
  | Pkcs1Sha384
  | Pkcs1Sha512

(** RSASSA-PKCS1-V1_5-VERIFY (RFC 8017 8.2.2) by an [rsaEncryption] key
    [(modulus, exponent)]: the signature, read as a big-endian integer below
    the modulus, raised to the exponent, is exactly the EMSA-PKCS1-v1_5
    encoding (RFC 8017 9.2) of the message's DigestInfo.  Used only for
    certificate signatures; TLS 1.3 never signs handshakes with it. *)
val rsa_pkcs1_verify:
  hash:pkcs1_hash ->
  modulus:B.bytes ->
  exponent:B.bytes ->
  message:B.bytes ->
  signature:signature ->
  GTot bool

(** ECDSA-VERIFY over P-256 with SHA-256 -- [ecdsa_secp256r1_sha256] -- by the
    affine point [point = x || y], of a DER-encoded signature. *)
val ecdsa_secp256r1_sha256_verify:
  point:B.bytes ->
  message:B.bytes ->
  signature:signature ->
  GTot bool

(** ECDSA-VERIFY over P-256 with SHA-384 (the hash truncated to the group
    order's 256 bits, FIPS 186-5 6.4.2), of a DER-encoded signature.  Used
    only for certificate signatures ([ecdsa-with-SHA384] by a P-256 key). *)
val ecdsa_secp256r1_sha384_verify:
  point:B.bytes ->
  message:B.bytes ->
  signature:signature ->
  GTot bool

(** ECDSA-VERIFY over P-384 with SHA-384 by the affine point
    [point = x || y], of a DER-encoded signature: TLS [ecdsa_secp384r1_sha384]
    and certificate [ecdsa-with-SHA384] by a P-384 key. *)
val ecdsa_secp384r1_sha384_verify:
  point:B.bytes ->
  message:B.bytes ->
  signature:signature ->
  GTot bool

(** ECDSA-VERIFY over P-384 with SHA-256 (the 256-bit digest is shorter than
    the order, so it is used whole), of a DER-encoded signature.  Used only
    for certificate signatures ([ecdsa-with-SHA256] by a P-384 key). *)
val ecdsa_secp384r1_sha256_verify:
  point:B.bytes ->
  message:B.bytes ->
  signature:signature ->
  GTot bool

val verify_signature:
  scheme:T.signature_scheme ->
  public_key:public_key ->
  message:B.bytes ->
  signature:signature ->
  GTot bool

val lemma_verify_signature_def:
  scheme:T.signature_scheme ->
  public_key:public_key ->
  message:B.bytes ->
  signature:signature ->
  Lemma
    (verify_signature scheme public_key message signature ==
      (match scheme, certificate_raw_public_key public_key with
       | T.Rsa_pss_rsae_sha256, Some (RawRsa modulus exponent) ->
         rsa_pss_rsae_sha256_verify modulus exponent message signature
       | T.Ecdsa_secp256r1_sha256, Some (RawP256 point) ->
         ecdsa_secp256r1_sha256_verify point message signature
       | T.Ecdsa_secp384r1_sha384, Some (RawP384 point) ->
         ecdsa_secp384r1_sha384_verify point message signature
       | _, _ -> false))

(* The signature scheme a credential can produce, as a function of the
   credential's public key.  A TLS 1.3 credential's algorithm is determined by
   its SubjectPublicKeyInfo -- an RSA key can only produce rsa_pss_rsae_sha256
   in this profile and a P-256 key only ecdsa_secp256r1_sha256 -- so this is a
   function of the identity rather than an extra field the configuration has to
   carry.  It is what makes the server's CertificateVerify algorithm agile
   (parity gap G5) without indexing the credential predicate by a scheme.
   The server only loads credentials with an RSA or P-256 key, so the default
   case is never used for a loaded credential. *)
val credential_signature_scheme:
  public_key:public_key ->
  Tot T.signature_scheme

val lemma_credential_signature_scheme_def:
  public_key:public_key ->
  Lemma
    (ensures
      credential_signature_scheme public_key ==
        (match certificate_raw_public_key public_key with
         | Some (RawP256 _) -> T.Ecdsa_secp256r1_sha256
         | _ -> T.Rsa_pss_rsae_sha256))

(* The profile implements exactly two credential algorithms, so a runtime query
   of the credential's scheme has only two answers to distinguish. *)
val lemma_credential_signature_scheme_supported:
  public_key:public_key ->
  Lemma
    (ensures
      credential_signature_scheme public_key == T.Rsa_pss_rsae_sha256 \/
      credential_signature_scheme public_key == T.Ecdsa_secp256r1_sha256)
    [SMTPat (credential_signature_scheme public_key)]
