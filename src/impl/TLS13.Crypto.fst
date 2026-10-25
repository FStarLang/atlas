module TLS13.Crypto

(**
  The cryptographic primitives, implemented by calling hacl-pulse directly.

  Every function here views its public-byte ([FStar.UInt8.t]) arrays as
  hacl-pulse secret-byte arrays ([TLS13.Crypto.Secret.secret], the same
  pointer), calls the hacl-pulse function, and proves the result is the
  [TLS13.Crypto.Spec] value, whose definitions are hacl-pulse's
  specifications.  The specification is total and the hacl-pulse functions
  are not, so each function first checks the same length bounds as the
  specification and, outside them, produces the specification's fallback
  value (zeros or failure).

  Calls into hacl-pulse are never in tail position: Custard currently
  eta-reduces a tail call to a linked function into a partial application.
**)

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

friend TLS13.Crypto.Spec

module A = Pulse.Lib.Array
module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CL = TLS13.ConnectionLog
module CS = TLS13.Crypto.Secret
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast
module S8 = Hacl.Secret.UInt8
module SB = Spec.Byte
module Copy = Hacl.Impl.Copy
module Sub = Hacl.Impl.Sub
module Mem = Hacl.Mem

(** {2 Sequence facts} *)

(** The bounds hacl-pulse's HMAC and HKDF preconditions need, stated per
    call so that no [pow2 61] equation reaches the solver's context (it
    derails the [pow2 16] reasoning behind every [size_t] literal). *)
let hmac_limits (k m: nat)
  : Lemma (requires k <= 65535 /\ m <= 65471)
          (ensures k < pow2 61 /\ SZ.fits (Spec.SHA2.block_len #Hacl.Secret.UInt32.t + m) /\
                   Spec.SHA2.block_len #Hacl.Secret.UInt32.t + m < pow2 61)
  = assert_norm (pow2 16 == 65536);
    SZ.fits_at_least_16 (64 + m);
    C.sha2_facts ()

let expand_limits (p i: nat)
  : Lemma (requires p <= 65535 /\ i <= 514)
          (ensures p < pow2 61 /\
                   Spec.SHA2.block_len #Hacl.Secret.UInt32.t + 32 + i + 1 < pow2 61 /\
                   SZ.fits (Spec.SHA2.block_len #Hacl.Secret.UInt32.t + 32 + i + 1))
  = assert_norm (pow2 16 == 65536);
    SZ.fits_at_least_16 (64 + 32 + i + 1);
    C.sha2_facts ()


let declassify_ext (s: Seq.seq S8.t) (t: B.bytes)
  : Lemma (requires Seq.length s == Seq.length t /\
                    (forall (i: nat). i < Seq.length s ==>
                       S8.v (Seq.index s i) == U8.v (Seq.index t i)))
          (ensures CS.declassify_seq s == t)
  = let aux (i: nat { i < Seq.length s })
      : Lemma (Seq.index (CS.declassify_seq s) i == Seq.index t i)
      = U8.v_inj (Seq.index (CS.declassify_seq s) i) (Seq.index t i) in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro (CS.declassify_seq s) t

let declassify_zeros (n: nat)
  : Lemma (CS.declassify_seq (Seq.create n (S8.classify 0uy)) == B.zeros n)
  = declassify_ext (Seq.create n (S8.classify 0uy)) (B.zeros n)

let classify_equal (a b: B.bytes)
  : Lemma (Seq.equal (CS.classify_seq a) (CS.classify_seq b) <==> Seq.equal a b)
  = let l1 () : Lemma (requires Seq.equal (CS.classify_seq a) (CS.classify_seq b))
                      (ensures Seq.equal a b)
      = Seq.lemma_eq_elim (CS.classify_seq a) (CS.classify_seq b);
        CS.declassify_classify a; CS.declassify_classify b in
    let l2 () : Lemma (requires Seq.equal a b)
                      (ensures Seq.equal (CS.classify_seq a) (CS.classify_seq b))
      = Seq.lemma_eq_elim a b in
    FStar.Classical.move_requires l1 ();
    FStar.Classical.move_requires l2 ()

let of_elems_vals (a: Seq.seq S8.t)
  : Lemma (CS.of_elems (SB.vals a) == CS.declassify_seq a)
  = SB.secrets_vals a

let of_elems_vals2 (a b: Seq.seq S8.t)
  : Lemma (CS.of_elems (Seq.append (SB.vals a) (SB.vals b)) ==
           CS.declassify_seq (Seq.append a b))
  = Seq.lemma_eq_intro (Seq.append (SB.vals a) (SB.vals b)) (SB.vals (Seq.append a b));
    SB.secrets_vals (Seq.append a b)

(** The pointwise postconditions of [Hacl.Impl.Copy] and [Hacl.Impl.Sub],
    turned into the sequence equalities the specification needs. *)
let seal_combine (n: nat) (vct vtag w vo: Seq.seq S8.t)
  : Lemma (requires Seq.length vct == n /\ Seq.length vtag == 16 /\
                    Seq.length w == n + 16 /\ Seq.length vo == n + 16 /\
                    (forall (k: nat). k < n ==> Seq.index w k == Seq.index vct k) /\
                    (forall (k: nat). k < n ==> Seq.index vo k == Seq.index w k) /\
                    (forall (k: nat). k < 16 ==> Seq.index vo (n + k) == Seq.index vtag k))
          (ensures vo == Seq.append vct vtag)
  = let aux (k: nat { k < n + 16 })
      : Lemma (Seq.index vo k == Seq.index (Seq.append vct vtag) k)
      = if k < n then () else assert (Seq.index vo (n + (k - n)) == Seq.index vtag (k - n)) in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro vo (Seq.append vct vtag)

let window_eq (n m: nat) (a b: Seq.seq S8.t)
  : Lemma (requires Seq.length a == m /\ n + m <= Seq.length b /\
                    (forall (k: nat). k < m ==> Seq.index a k == Seq.index b (n + k)))
          (ensures a == Seq.slice b n (n + m))
  = Seq.lemma_eq_intro a (Seq.slice b n (n + m))

let prefix_eq (n: nat) (a b: Seq.seq S8.t)
  : Lemma (requires n <= Seq.length a /\ n <= Seq.length b /\
                    (forall (k: nat). k < n ==> Seq.index a k == Seq.index b k))
          (ensures Seq.slice a 0 n == Seq.slice b 0 n)
  = Seq.lemma_eq_intro (Seq.slice a 0 n) (Seq.slice b 0 n)

(** [n < 2^61], checked without constants that do not fit a 16-bit [size_t]. *)
let below_pow2_61 (n: nat)
  : Lemma (n / 32768 / 32768 / 32768 / 32768 < 2 <==> n < pow2 61)
  = FStar.Math.Lemmas.division_multiplication_lemma n 32768 32768;
    FStar.Math.Lemmas.division_multiplication_lemma n (32768 * 32768) 32768;
    FStar.Math.Lemmas.division_multiplication_lemma n (32768 * 32768 * 32768) 32768;
    assert_norm (pow2 61 == 2 * (32768 * 32768 * 32768 * 32768))


(** {2 Helpers} *)

fn zero_fill (a: array U8.t) (n: SZ.t)
  requires pts_to a 'old ** pure (Seq.length 'old == SZ.v n)
  ensures pts_to a (B.zeros (SZ.v n))
{
  CS.to_secret a;
  Copy.fill (CS.secret a) (S8.classify 0uy) n;
  CS.of_secret a;
  declassify_zeros (SZ.v n);
  ()
}

inline_for_extraction
fn below_pow2_61_sz (n: SZ.t)
  returns b: bool
  ensures pure (b <==> SZ.v n < pow2 61)
{
  let q1 = SZ.div n 32768sz;
  let q2 = SZ.div q1 32768sz;
  let q3 = SZ.div q2 32768sz;
  let q4 = SZ.div q3 32768sz;
  below_pow2_61 (SZ.v n);
  SZ.lt q4 2sz
}

inline_for_extraction
fn hmac_in_range_sz (k m: SZ.t)
  returns b: bool
  ensures pure (b <==> (SZ.v k <= 65535 /\ SZ.v m <= 65471))
{
  (SZ.lte k 65535sz && SZ.lte m 65471sz)
}

inline_for_extraction
fn aead_in_range_sz (p a: SZ.t)
  returns b: bool
  ensures pure (b <==> (SZ.v p <= C.aead_max_len /\ SZ.v a <= C.aead_max_len))
{
  (SZ.lte p 65280sz && SZ.lte a 65280sz)
}

(** {2 Randomness} *)

fn random_bytes (out: array U8.t) (out_len: SZ.t)
  requires pts_to out 'old ** pure (B.length 'old == SZ.v out_len)
  returns ok: bool
  ensures exists* bytes. pts_to out bytes ** pure (B.length bytes == SZ.v out_len)
{
  TLS13.Crypto.Random.random_bytes out out_len
}

(** {2 Hashing} *)

fn hash_prefix (input: array U8.t) (input_len: SZ.t) (out: array U8.t)
  requires pts_to input 'msg **
           pts_to out 'old **
           pure (SZ.v input_len <= B.length 'msg /\
                 B.length 'old == 32)
  ensures pts_to input 'msg **
          pts_to out (C.sha256 (CL.raw_slice 'msg 0 (SZ.v input_len)))
{
  let small = below_pow2_61_sz input_len;
  let m = Ghost.hide (Seq.slice 'msg 0 (SZ.v input_len));
  C.sha256_eq m;
  if small {
    CS.to_secret input;
    CS.to_secret out;
    A.pts_to_len (CS.secret input);
    let s = Sub.sub (CS.secret input) 0sz input_len;
    CS.classify_slice 'msg 0 (SZ.v input_len);
    Hacl.Hash.SHA2.sha256 (CS.secret out) s input_len;
    Sub.unsub_id (CS.secret input) 0 (SZ.v input_len) s;
    CS.of_secret input;
    CS.of_secret out;
    ()
  } else {
    zero_fill out 32sz;
    ()
  }
}

fn sha256 (input: array U8.t) (input_len: SZ.t) (out: array U8.t)
  requires pts_to input 'msg **
           pts_to out 'old **
           pure (B.length 'msg == SZ.v input_len /\ B.length 'old == 32)
  ensures pts_to input 'msg ** pts_to out (C.sha256 'msg)
{
  hash_prefix input input_len out;
  assert pure (Seq.equal (CL.raw_slice 'msg 0 (SZ.v input_len)) 'msg);
  ()
}

fn sha256_prefix (input: array U8.t) (input_len: SZ.t) (out: array U8.t)
  requires pts_to input 'msg **
           pts_to out 'old **
           pure (SZ.v input_len <= B.length 'msg /\
                 B.length 'old == 32)
  ensures pts_to input 'msg **
          pts_to out (C.sha256 (CL.raw_slice 'msg 0 (SZ.v input_len)))
{
  hash_prefix input input_len out
}

fn sha256_empty (out: array U8.t)
  requires pts_to out 'old **
           pure (B.length 'old == 32)
  ensures pts_to out (C.sha256 B.empty)
{
  let mut e = [| 0uy; 1sz |];
  hash_prefix e 0sz out;
  assert pure (Seq.equal (CL.raw_slice (Seq.create 1 0uy) 0 0) B.empty);
  ()
}

(** {2 HMAC and HKDF} *)

fn hmac_sha256 (key: array U8.t) (key_len: SZ.t) (msg: array U8.t) (msg_len: SZ.t) (out: array U8.t)
  requires pts_to key 'key_bytes **
           pts_to msg 'msg_bytes **
           pts_to out 'old **
           pure (B.length 'key_bytes == SZ.v key_len /\
                 B.length 'msg_bytes == SZ.v msg_len /\
                 B.length 'old == 32)
  ensures pts_to key 'key_bytes **
          pts_to msg 'msg_bytes **
          pts_to out (C.hmac_sha256 'key_bytes 'msg_bytes)
{
  C.hmac_sha256_eq 'key_bytes 'msg_bytes;
  let ok = hmac_in_range_sz key_len msg_len;
  if ok {
    hmac_limits (SZ.v key_len) (SZ.v msg_len);
    CS.to_secret key;
    CS.to_secret msg;
    CS.to_secret out;
    Hacl.HMAC.hmac_sha256 (CS.secret out) (CS.secret key) key_len (CS.secret msg) msg_len;
    CS.of_secret key;
    CS.of_secret msg;
    CS.of_secret out;
    ()
  } else {
    zero_fill out 32sz;
    ()
  }
}

fn equal32 (a: array U8.t) (b: array U8.t)
  requires pts_to a 'a_bytes **
           pts_to b 'b_bytes **
           pure (B.length 'a_bytes == 32 /\ B.length 'b_bytes == 32)
  returns ok: bool
  ensures pts_to a 'a_bytes **
          pts_to b 'b_bytes **
          pure (ok <==> Seq.equal 'a_bytes 'b_bytes)
{
  CS.to_secret a;
  CS.to_secret b;
  let ok = Hacl.Impl.Bytes.bytes_eq (CS.secret a) (CS.secret b) 32sz;
  CS.of_secret a;
  CS.of_secret b;
  classify_equal 'a_bytes 'b_bytes;
  ok
}

fn equal12 (a: array U8.t) (b: array U8.t)
  requires pts_to a 'a_bytes **
           pts_to b 'b_bytes **
           pure (B.length 'a_bytes == 12 /\ B.length 'b_bytes == 12)
  returns ok: bool
  ensures pts_to a 'a_bytes **
          pts_to b 'b_bytes **
          pure (ok <==> Seq.equal 'a_bytes 'b_bytes)
{
  CS.to_secret a;
  CS.to_secret b;
  let ok = Hacl.Impl.Bytes.bytes_eq (CS.secret a) (CS.secret b) 12sz;
  CS.of_secret a;
  CS.of_secret b;
  classify_equal 'a_bytes 'b_bytes;
  ok
}

fn hkdf_extract (salt: array U8.t) (salt_len: SZ.t) (ikm: array U8.t) (ikm_len: SZ.t) (out: array U8.t)
  requires pts_to salt 'salt_bytes **
           pts_to ikm 'ikm_bytes **
           pts_to out 'old **
           pure (B.length 'salt_bytes == SZ.v salt_len /\
                 B.length 'ikm_bytes == SZ.v ikm_len /\
                 B.length 'old == 32)
  ensures pts_to salt 'salt_bytes **
          pts_to ikm 'ikm_bytes **
          pts_to out (C.hkdf_extract 'salt_bytes 'ikm_bytes)
{
  C.hkdf_extract_eq 'salt_bytes 'ikm_bytes;
  let ok = hmac_in_range_sz salt_len ikm_len;
  if ok {
    hmac_limits (SZ.v salt_len) (SZ.v ikm_len);
    CS.to_secret salt;
    CS.to_secret ikm;
    CS.to_secret out;
    Hacl.HKDF.extract_sha256 (CS.secret out) (CS.secret salt) salt_len (CS.secret ikm) ikm_len;
    CS.of_secret salt;
    CS.of_secret ikm;
    CS.of_secret out;
    ()
  } else {
    zero_fill out 32sz;
    ()
  }
}

fn hkdf_expand
  (secret: array U8.t)
  (info: array U8.t)
  (info_len: SZ.t)
  (out: array U8.t)
  (out_len: SZ.t)
  (#lbl: erased B.bytes)
  (#context: erased B.bytes)
  requires pts_to secret 'secret_bytes **
          pts_to info 'info_bytes **
          pts_to out 'old **
          pure (B.length 'secret_bytes == 32 /\
                B.length 'info_bytes == 520 /\
                B.length 'old == SZ.v out_len /\
                B.length (Ghost.reveal lbl) <= 249 /\
                B.length (Ghost.reveal context) <= 255 /\
                SZ.v out_len <= 8160 /\
                SZ.v info_len ==
                  C.hkdf_label_info_length
                    (Ghost.reveal lbl)
                    (Ghost.reveal context) /\
                'info_bytes ==
                  C.hkdf_label_info_buffer
                    (Ghost.reveal lbl)
                    (Ghost.reveal context)
                    (SZ.v out_len))
  ensures pts_to secret 'secret_bytes **
          pts_to info 'info_bytes **
          pure (B.length
                 (C.hkdf_expand_label
                   'secret_bytes
                   (Ghost.reveal lbl)
                   (Ghost.reveal context)
                   (SZ.v out_len)) == SZ.v out_len) **
          pts_to out (C.hkdf_expand_label
                       'secret_bytes
                       (Ghost.reveal lbl)
                       (Ghost.reveal context)
                       (SZ.v out_len))
{
  let prk_len = 32sz;
  C.hkdf_expand_label_eq 'secret_bytes lbl context (SZ.v out_len);
  expand_limits 32 (SZ.v info_len);
  CS.to_secret secret;
  CS.to_secret info;
  CS.to_secret out;
  A.pts_to_len (CS.secret info);
  A.pts_to_len (CS.secret out);
  let i = Sub.sub (CS.secret info) 0sz info_len;
  CS.classify_slice 'info_bytes 0 (SZ.v info_len);
  Hacl.HKDF.expand_sha256 (CS.secret out) out_len (CS.secret secret) prk_len i info_len;
  Sub.unsub_id (CS.secret info) 0 (SZ.v info_len) i;
  CS.of_secret secret;
  CS.of_secret info;
  CS.of_secret out;
  ()
}

(** {2 X25519} *)

fn x25519_public_from_private (sk: array U8.t) (out: array U8.t)
  requires pts_to sk 'sk_bytes **
           pts_to out 'old **
           pure (B.length 'sk_bytes == 32 /\ B.length 'old == 32)
  ensures pts_to sk 'sk_bytes ** pts_to out (C.x25519_public_from_private 'sk_bytes)
{
  C.x25519_public_from_private_eq 'sk_bytes;
  CS.to_secret sk;
  CS.to_secret out;
  Hacl.Curve25519.secret_to_public (CS.secret out) (CS.secret sk);
  CS.of_secret sk;
  CS.of_secret out;
  ()
}

fn x25519_ecdh (sk: array U8.t) (pk: array U8.t) (out: array U8.t)
  requires pts_to sk 'sk_bytes **
           pts_to pk 'pk_bytes **
           pts_to out 'old **
           pure (B.length 'sk_bytes == 32 /\ B.length 'pk_bytes == 32 /\ B.length 'old == 32)
  returns ok: bool
  ensures exists* out_bytes.
          pts_to sk 'sk_bytes **
          pts_to pk 'pk_bytes **
          pts_to out out_bytes **
          pure (B.length out_bytes == 32 /\
                (ok ==> Some? (C.x25519_shared 'sk_bytes 'pk_bytes) /\
                        Some?.v (C.x25519_shared 'sk_bytes 'pk_bytes) == out_bytes) /\
                (not ok ==> None? (C.x25519_shared 'sk_bytes 'pk_bytes)))
{
  C.x25519_shared_eq 'sk_bytes 'pk_bytes;
  CS.to_secret sk;
  CS.to_secret pk;
  CS.to_secret out;
  let ok = Hacl.Curve25519.ecdh (CS.secret out) (CS.secret sk) (CS.secret pk);
  CS.of_secret sk;
  CS.of_secret pk;
  CS.of_secret out;
  ok
}

fn x25519_shared (sk: array U8.t) (pk: array U8.t) (out: array U8.t)
  requires pts_to sk 'sk_bytes **
           pts_to pk 'pk_bytes **
           pts_to out 'old **
           pure (B.length 'sk_bytes == 32 /\ B.length 'pk_bytes == 32 /\ B.length 'old == 32)
  returns ok: bool
  ensures pts_to sk 'sk_bytes **
          pts_to pk 'pk_bytes **
          (exists* shared.
            pts_to out shared **
            pure (B.length shared == 32 /\
                  (ok ==>
                   Some? (C.x25519_shared 'sk_bytes 'pk_bytes) /\
                   Some?.v (C.x25519_shared 'sk_bytes 'pk_bytes) == shared) /\
                  (not ok ==> C.x25519_shared 'sk_bytes 'pk_bytes == None)))
{
  x25519_ecdh sk pk out
}

let x25519_shared_call sk pk shared ok =
  B.length shared == 32 /\
  (ok ==> Some? (C.x25519_shared sk pk) /\ Some?.v (C.x25519_shared sk pk) == shared) /\
  (not ok ==> None? (C.x25519_shared sk pk))

let lemma_x25519_shared_call_success sk pk shared ok = ()

fn x25519_shared_runtime (sk: array U8.t) (pk: array U8.t) (out: array U8.t)
  requires pts_to sk 'sk_bytes **
           pts_to pk 'pk_bytes **
           pts_to out 'old **
           pure (B.length 'sk_bytes == 32 /\ B.length 'pk_bytes == 32 /\ B.length 'old == 32)
  returns ok: bool
  ensures exists* out_bytes.
          pts_to sk 'sk_bytes **
          pts_to pk 'pk_bytes **
          pts_to out out_bytes **
          pure (x25519_shared_call 'sk_bytes 'pk_bytes out_bytes ok)
{
  x25519_ecdh sk pk out
}

(** {2 P-256} *)

fn p256_public_from_private (sk: array U8.t) (out: array U8.t)
  requires pts_to sk 'sk_bytes **
           pts_to out 'old **
           pure (B.length 'sk_bytes == 32 /\ B.length 'old == 65)
  ensures pts_to sk 'sk_bytes ** pts_to out (C.p256_public_from_private 'sk_bytes)
{
  C.p256_public_from_private_eq 'sk_bytes;
  CS.to_secret sk;
  let zraw : S8.t = S8.classify 0uy;
    let mut raw = [| zraw; 64sz |];
  let ok = Hacl.P256.Ecdh.dh_initiator raw (CS.secret sk);
  CS.of_secret sk;
  if ok {
    CS.to_secret out;
    Hacl.P256.Sec1.raw_to_uncompressed (CS.secret out) raw;
    CS.of_secret out;
    ()
  } else {
    zero_fill out 65sz;
    ()
  }
}

let p256_shared_call sk pk shared ok =
  B.length shared == 32 /\
  (ok ==> Some? (C.p256_shared sk pk) /\ Some?.v (C.p256_shared sk pk) == shared) /\
  (not ok ==> None? (C.p256_shared sk pk))

let lemma_p256_shared_call_success sk pk shared ok = ()

fn p256_shared_runtime (sk: array U8.t) (pk: array U8.t) (out: array U8.t)
  requires pts_to sk 'sk_bytes **
           pts_to pk 'pk_bytes **
           pts_to out 'old **
           pure (B.length 'sk_bytes == 32 /\ B.length 'pk_bytes == 65 /\ B.length 'old == 32)
  returns ok: bool
  ensures exists* out_bytes.
          pts_to sk 'sk_bytes **
          pts_to pk 'pk_bytes **
          pts_to out out_bytes **
          pure (p256_shared_call 'sk_bytes 'pk_bytes out_bytes ok)
{
  C.p256_shared_eq 'sk_bytes 'pk_bytes;
  CS.to_secret pk;
  let zraw : S8.t = S8.classify 0uy;
    let mut raw = [| zraw; 64sz |];
  let ok1 = Hacl.P256.Sec1.uncompressed_to_raw raw (CS.secret pk);
  CS.of_secret pk;
  if ok1 {
    CS.to_secret sk;
    let zsh : S8.t = S8.classify 0uy;
    let mut sh = [| zsh; 64sz |];
    Mem.track sh;
    let ok2 = Hacl.P256.Ecdh.dh_responder sh raw (CS.secret sk);
    CS.of_secret sk;
    with vsh. assert (A.pts_to sh vsh);
    if ok2 {
      CS.to_secret out;
      A.pts_to_len (CS.secret out);
      Copy.copy_prefix (CS.secret out) sh 32sz;
      with vo. assert (A.pts_to (CS.secret out) vo);
      window_eq 0 32 vo vsh;
      CS.of_secret out;
      Mem.wipe sh 64sz;
      true
    } else {
      Mem.wipe sh 64sz;
      false
    }
  } else {
    false
  }
}

(** {2 AEAD} *)

fn chacha20_poly1305_seal
  (key: array U8.t)
  (nonce: array U8.t)
  (aad: array U8.t)
  (aad_len: SZ.t)
  (plain: array U8.t)
  (plain_len: SZ.t)
  (out: array U8.t)
  requires pts_to key 'key_bytes **
           pts_to nonce 'nonce_bytes **
           pts_to aad 'aad_bytes **
           pts_to plain 'plain_bytes **
           pts_to out 'old **
           pure (B.length 'key_bytes == 32 /\
                 B.length 'nonce_bytes == 12 /\
                 B.length 'aad_bytes == SZ.v aad_len /\
                 B.length 'plain_bytes == SZ.v plain_len /\
                 B.length 'old == SZ.v plain_len + 16)
  ensures pts_to key 'key_bytes **
          pts_to nonce 'nonce_bytes **
          pts_to aad 'aad_bytes **
          pts_to plain 'plain_bytes **
          pts_to out (C.aead_seal C.AEAD_CHACHA20_POLY1305 'key_bytes 'nonce_bytes 'aad_bytes 'plain_bytes)
{
  C.aead_seal_eq C.AEAD_CHACHA20_POLY1305 'key_bytes 'nonce_bytes 'aad_bytes 'plain_bytes;
  C.aead_limits ();
  let in_range = aead_in_range_sz plain_len aad_len;
  if in_range {
    CS.to_secret key;
    CS.to_secret nonce;
    CS.to_secret aad;
    CS.to_secret plain;
    CS.to_secret out;
    A.pts_to_len (CS.secret out);
    let ztag : S8.t = S8.classify 0uy;
    let mut tag = [| ztag; 16sz |];
    let ct = Sub.sub (CS.secret out) 0sz plain_len;
    Hacl.Chacha20Poly1305.encrypt ct tag (CS.secret plain) plain_len (CS.secret aad) aad_len
      (CS.secret key) (CS.secret nonce);
    with vct vtag. assert (A.pts_to ct vct ** A.pts_to tag vtag);
    Sub.unsub (CS.secret out) 0 (SZ.v plain_len) ct;
    with w. assert (A.pts_to (CS.secret out) w);
    Copy.copy_at (CS.secret out) plain_len tag 16sz;
    with vo. assert (A.pts_to (CS.secret out) vo);
    seal_combine (SZ.v plain_len) vct vtag w vo;
    CS.of_secret key;
    CS.of_secret nonce;
    CS.of_secret aad;
    CS.of_secret plain;
    CS.of_secret out;
    ()
  } else {
    A.pts_to_len out;
    zero_fill out (SZ.add plain_len 16sz);
    ()
  }
}

let chacha_open_post (key nonce aad cipher old: B.bytes) (ok: bool) (vmsg: Seq.seq S8.t)
  : Lemma
    (requires (
      let n = B.length cipher in
      let len = n - 16 in
      B.length key == 32 /\ B.length nonce == 12 /\ n >= 16 /\ B.length old == len /\
      C.aead_open_in_range aad cipher /\
      Seq.length vmsg == len /\
      (ok <==> Spec.Chacha20Poly1305.decrypt_ok (CS.classify_seq key) (CS.classify_seq nonce)
                 (CS.classify_seq aad) (CS.classify_seq (Seq.slice cipher 0 len))
                 (CS.classify_seq (Seq.slice cipher len n))) /\
      (if ok then vmsg == Spec.Chacha20Poly1305.decrypted (CS.classify_seq key)
                            (CS.classify_seq nonce) (CS.classify_seq (Seq.slice cipher 0 len))
       else vmsg == CS.classify_seq old)))
    (ensures (
      let r = C.aead_open C.AEAD_CHACHA20_POLY1305 key nonce aad cipher in
      (ok ==> Some? r /\ CS.declassify_seq vmsg == Some?.v r) /\
      (not ok ==> r == None /\ CS.declassify_seq vmsg == old)))
  = C.aead_open_eq C.AEAD_CHACHA20_POLY1305 key nonce aad cipher;
    CS.declassify_classify old;
    assert (C.norm 32 key == key);
    assert (C.norm 12 nonce == nonce)

let aead_open_out_of_range (alg: C.aead_alg) (key nonce aad cipher: B.bytes)
  : Lemma (requires not (C.aead_open_in_range aad cipher))
          (ensures C.aead_open alg key nonce aad cipher == None)
  = C.aead_open_eq alg key nonce aad cipher

fn chacha20_poly1305_open
  (key: array U8.t)
  (nonce: array U8.t)
  (aad: array U8.t)
  (aad_len: SZ.t)
  (cipher: array U8.t)
  (cipher_len: SZ.t)
  (out: array U8.t)
  requires pts_to key 'key_bytes **
           pts_to nonce 'nonce_bytes **
           pts_to aad 'aad_bytes **
           pts_to cipher 'cipher_bytes **
           pts_to out 'old **
           pure (B.length 'key_bytes == 32 /\
                 B.length 'nonce_bytes == 12 /\
                 B.length 'aad_bytes == SZ.v aad_len /\
                 B.length 'cipher_bytes == SZ.v cipher_len /\
                 B.length 'old + 16 == SZ.v cipher_len)
  returns ok: bool
  ensures exists* out_bytes.
          pts_to key 'key_bytes **
          pts_to nonce 'nonce_bytes **
          pts_to aad 'aad_bytes **
          pts_to cipher 'cipher_bytes **
          pts_to out out_bytes **
          pure ((ok ==> Some? (C.aead_open C.AEAD_CHACHA20_POLY1305 'key_bytes 'nonce_bytes 'aad_bytes 'cipher_bytes) /\
                        out_bytes == Some?.v (C.aead_open C.AEAD_CHACHA20_POLY1305 'key_bytes 'nonce_bytes 'aad_bytes 'cipher_bytes)) /\
                (not ok ==> C.aead_open C.AEAD_CHACHA20_POLY1305 'key_bytes 'nonce_bytes 'aad_bytes 'cipher_bytes == None /\
                            out_bytes == 'old))
{
  C.aead_limits ();
  let len = SZ.sub cipher_len 16sz;
  let in_range = aead_in_range_sz len aad_len;
  if in_range {
    CS.to_secret key;
    CS.to_secret nonce;
    CS.to_secret aad;
    CS.to_secret cipher;
    CS.to_secret out;
    A.pts_to_len (CS.secret cipher);
    let ztag : S8.t = S8.classify 0uy;
    let mut tag = [| ztag; 16sz |];
    Copy.copy_range tag 0sz (CS.secret cipher) len 16sz;
    with vtag. assert (A.pts_to tag vtag);
    CS.classify_slice 'cipher_bytes (SZ.v len) (SZ.v cipher_len);
    window_eq (SZ.v len) 16 vtag (CS.classify_seq 'cipher_bytes);
    let ct = Sub.sub (CS.secret cipher) 0sz len;
    CS.classify_slice 'cipher_bytes 0 (SZ.v len);
    let ok = Hacl.Chacha20Poly1305.decrypt (CS.secret out) ct len tag (CS.secret aad) aad_len
               (CS.secret key) (CS.secret nonce);
    Sub.unsub_id (CS.secret cipher) 0 (SZ.v len) ct;
    with vmsg. assert (A.pts_to (CS.secret out) vmsg);
    chacha_open_post 'key_bytes 'nonce_bytes 'aad_bytes 'cipher_bytes 'old ok vmsg;
    CS.of_secret key;
    CS.of_secret nonce;
    CS.of_secret aad;
    CS.of_secret cipher;
    CS.of_secret out;
    ok
  } else {
    aead_open_out_of_range C.AEAD_CHACHA20_POLY1305 'key_bytes 'nonce_bytes 'aad_bytes 'cipher_bytes;
    false
  }
}

fn aes128_gcm_seal
  (key: array U8.t)
  (nonce: array U8.t)
  (aad: array U8.t)
  (aad_len: SZ.t)
  (plain: array U8.t)
  (plain_len: SZ.t)
  (out: array U8.t)
  requires pts_to key 'key_bytes **
           pts_to nonce 'nonce_bytes **
           pts_to aad 'aad_bytes **
           pts_to plain 'plain_bytes **
           pts_to out 'old **
           pure (B.length 'key_bytes == 16 /\
                 B.length 'nonce_bytes == 12 /\
                 B.length 'aad_bytes == SZ.v aad_len /\
                 B.length 'plain_bytes == SZ.v plain_len /\
                 B.length 'old == SZ.v plain_len + 16)
  ensures pts_to key 'key_bytes **
          pts_to nonce 'nonce_bytes **
          pts_to aad 'aad_bytes **
          pts_to plain 'plain_bytes **
          pts_to out (C.aead_seal C.AEAD_AES128_GCM 'key_bytes 'nonce_bytes 'aad_bytes 'plain_bytes)
{
  C.aead_seal_eq C.AEAD_AES128_GCM 'key_bytes 'nonce_bytes 'aad_bytes 'plain_bytes;
  C.aead_limits ();
  let in_range = aead_in_range_sz plain_len aad_len;
  if in_range {
    CS.to_secret key;
    CS.to_secret nonce;
    CS.to_secret aad;
    CS.to_secret plain;
    CS.to_secret out;
    A.pts_to_len (CS.secret out);
    Copy.copy_at (CS.secret out) 0sz (CS.secret plain) plain_len;
    with vo0. assert (A.pts_to (CS.secret out) vo0);
    window_eq 0 (SZ.v plain_len) (CS.classify_seq 'plain_bytes) vo0;
    let ztag : S8.t = S8.classify 0uy;
    let mut tag = [| ztag; 16sz |];
    let m = Sub.sub (CS.secret out) 0sz plain_len;
    Hacl.AES.GCM.aes128_encrypt tag m plain_len (CS.secret key) (CS.secret nonce) 12sz
      (CS.secret aad) aad_len;
    with vm vtag. assert (A.pts_to m vm ** A.pts_to tag vtag);
    Sub.unsub (CS.secret out) 0 (SZ.v plain_len) m;
    with w. assert (A.pts_to (CS.secret out) w);
    Copy.copy_at (CS.secret out) plain_len tag 16sz;
    with vo. assert (A.pts_to (CS.secret out) vo);
    seal_combine (SZ.v plain_len) vm vtag w vo;
    of_elems_vals2 vm vtag;
    CS.of_secret key;
    CS.of_secret nonce;
    CS.of_secret aad;
    CS.of_secret plain;
    CS.of_secret out;
    ()
  } else {
    A.pts_to_len out;
    zero_fill out (SZ.add plain_len 16sz);
    ()
  }
}

let gcm_fits (a m: nat)
  : Lemma (requires a <= C.aead_max_len /\ m <= C.aead_max_len)
          (ensures SZ.fits 28 /\ SZ.fits (a + 16) /\ SZ.fits (m + 16))
  = assert_norm (pow2 16 == 65536);
    SZ.fits_at_least_16 28;
    SZ.fits_at_least_16 (a + 16);
    SZ.fits_at_least_16 (m + 16)

let gcm_open_post (key nonce aad cipher: B.bytes) (ok: bool) (vm: Seq.seq S8.t)
  : Lemma
    (requires (
      let n = B.length cipher in
      let len = n - 16 in
      B.length key == 16 /\ B.length nonce == 12 /\ n >= 16 /\
      C.aead_open_in_range aad cipher /\
      Seq.length vm == len /\
      Spec.GCM.iv_ok (SB.vals (CS.classify_seq nonce)) /\
      Spec.GCM.aad_ok (SB.vals (CS.classify_seq aad)) /\
      Spec.GCM.msg_ok (SB.vals (CS.classify_seq (Seq.slice cipher 0 len))) /\
      (let d = Spec.GCM.gcm_decrypt Spec.AES.AES128 (SB.vals (CS.classify_seq key))
                 (SB.vals (CS.classify_seq nonce)) (SB.vals (CS.classify_seq aad))
                 (SB.vals (CS.classify_seq (Seq.slice cipher 0 len)))
                 (SB.vals (CS.classify_seq (Seq.slice cipher len n))) in
       (ok ==> Some? d /\ SB.vals vm == Some?.v d) /\
       (not ok ==> None? d))))
    (ensures (
      let r = C.aead_open C.AEAD_AES128_GCM key nonce aad cipher in
      (ok ==> Some? r /\ CS.declassify_seq vm == Some?.v r) /\
      (not ok ==> r == None)))
  = C.aead_open_eq C.AEAD_AES128_GCM key nonce aad cipher;
    of_elems_vals vm;
    assert (C.norm 16 key == key);
    assert (C.norm 12 nonce == nonce)

fn aes128_gcm_open
  (key: array U8.t)
  (nonce: array U8.t)
  (aad: array U8.t)
  (aad_len: SZ.t)
  (cipher: array U8.t)
  (cipher_len: SZ.t)
  (out: array U8.t)
  requires pts_to key 'key_bytes **
           pts_to nonce 'nonce_bytes **
           pts_to aad 'aad_bytes **
           pts_to cipher 'cipher_bytes **
           pts_to out 'old **
           pure (B.length 'key_bytes == 16 /\
                 B.length 'nonce_bytes == 12 /\
                 B.length 'aad_bytes == SZ.v aad_len /\
                 B.length 'cipher_bytes == SZ.v cipher_len /\
                 B.length 'old + 16 == SZ.v cipher_len)
  returns ok: bool
  ensures exists* out_bytes.
          pts_to key 'key_bytes **
          pts_to nonce 'nonce_bytes **
          pts_to aad 'aad_bytes **
          pts_to cipher 'cipher_bytes **
          pts_to out out_bytes **
          pure ((ok ==> Some? (C.aead_open C.AEAD_AES128_GCM 'key_bytes 'nonce_bytes 'aad_bytes 'cipher_bytes) /\
                        out_bytes == Some?.v (C.aead_open C.AEAD_AES128_GCM 'key_bytes 'nonce_bytes 'aad_bytes 'cipher_bytes)) /\
                (not ok ==> C.aead_open C.AEAD_AES128_GCM 'key_bytes 'nonce_bytes 'aad_bytes 'cipher_bytes == None /\
                            out_bytes == 'old))
{
  C.aead_limits ();
  let len = SZ.sub cipher_len 16sz;
  let in_range = aead_in_range_sz len aad_len;
  if in_range {
    CS.to_secret key;
    CS.to_secret nonce;
    CS.to_secret aad;
    CS.to_secret cipher;
    A.pts_to_len (CS.secret cipher);
    let ztag : S8.t = S8.classify 0uy;
    let mut tag = [| ztag; 16sz |];
    Copy.copy_range tag 0sz (CS.secret cipher) len 16sz;
    with vtag. assert (A.pts_to tag vtag);
    CS.classify_slice 'cipher_bytes (SZ.v len) (SZ.v cipher_len);
    window_eq (SZ.v len) 16 vtag (CS.classify_seq 'cipher_bytes);
    (* GCM decrypts in place and leaves the ciphertext behind on failure,
       but a failed open must leave [out] untouched: decrypt in a copy. *)
    let tmp = Mem.alloc #S8.t (S8.classify 0uy) cipher_len;
    Copy.copy_prefix tmp (CS.secret cipher) len;
    with vt0. assert (A.pts_to tmp vt0);
    CS.classify_slice 'cipher_bytes 0 (SZ.v len);
    prefix_eq (SZ.v len) vt0 (CS.classify_seq 'cipher_bytes);
    let m = Sub.sub tmp 0sz len;
    gcm_fits (SZ.v aad_len) (SZ.v len);
    let ok = Hacl.AES.GCM.aes128_decrypt m len tag (CS.secret key) (CS.secret nonce) 12sz
               (CS.secret aad) aad_len;
    with vm. assert (A.pts_to m vm);
    gcm_open_post 'key_bytes 'nonce_bytes 'aad_bytes 'cipher_bytes ok vm;
    if ok {
      CS.to_secret out;
      Copy.copy_exact (CS.secret out) m len;
      CS.of_secret out;
      Sub.unsub tmp 0 (SZ.v len) m;
      Mem.free tmp cipher_len;
      CS.of_secret key;
      CS.of_secret nonce;
      CS.of_secret aad;
      CS.of_secret cipher;
      true
    } else {
      Sub.unsub tmp 0 (SZ.v len) m;
      Mem.free tmp cipher_len;
      CS.of_secret key;
      CS.of_secret nonce;
      CS.of_secret aad;
      CS.of_secret cipher;
      false
    }
  } else {
    aead_open_out_of_range C.AEAD_AES128_GCM 'key_bytes 'nonce_bytes 'aad_bytes 'cipher_bytes;
    false
  }
}

(** {2 Signature verification} *)

(** Byte [k] of the 32-byte value of the INTEGER contents [w[off .. off+l)]. *)
let der_int_byte (w: B.bytes) (off l k: nat) : U8.t =
  if k + l < 32 then 0uy
  else if off + l + k - 32 < Seq.length w then Seq.index w (off + l + k - 32)
  else 0uy

let der_integer_32_value (w: B.bytes) (off l: nat) (o: Seq.seq U8.t)
  : Lemma (requires off + l <= Seq.length w /\
                    Some? (C.der_integer_32 (Seq.slice w off (off + l))) /\
                    Seq.length o == 32 /\
                    (forall (k: nat). k < 32 ==> Seq.index o k == der_int_byte w off l k))
          (ensures Some?.v (C.der_integer_32 (Seq.slice w off (off + l))) == o)
  = let v = Seq.slice w off (off + l) in
    let x = Some?.v (C.der_integer_32 v) in
    let aux (k: nat { k < 32 }) : Lemma (Seq.index x k == Seq.index o k)
      = if l = 33 then ()
        else if k + l < 32 then ()
        else assert (Seq.index x k == Seq.index v (k - (32 - l))) in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro x o

let der_decode_some (w: B.bytes) (n rl sl: nat) (vr vs: Seq.seq U8.t)
  : Lemma (requires n <= Seq.length w /\ 8 <= n /\ n <= 72 /\
                    Seq.index w 0 == 0x30uy /\ U8.v (Seq.index w 1) == n - 2 /\
                    Seq.index w 2 == 0x02uy /\ U8.v (Seq.index w 3) == rl /\
                    6 + rl <= n /\ Seq.index w (4 + rl) == 0x02uy /\
                    U8.v (Seq.index w (5 + rl)) == sl /\ 6 + rl + sl == n /\
                    Some? (C.der_integer_32 (CL.raw_slice w 4 (4 + rl))) /\
                    Some? (C.der_integer_32 (CL.raw_slice w (6 + rl) n)) /\
                    Seq.length vr == 32 /\ Seq.length vs == 32 /\
                    (forall (k: nat). k < 32 ==> Seq.index vr k == der_int_byte w 4 rl k) /\
                    (forall (k: nat). k < 32 ==> Seq.index vs k == der_int_byte w (6 + rl) sl k))
          (ensures C.ecdsa_signature_der_decode (CL.raw_slice w 0 n) == Some (vr, vs))
  = let v = Seq.slice w 0 n in
    Seq.slice_slice w 0 n 4 (4 + rl);
    Seq.slice_slice w 0 n (6 + rl) n;
    der_integer_32_value w 4 rl vr;
    der_integer_32_value w (6 + rl) sl vs;
    assert (Seq.index v 0 == Seq.index w 0);
    assert (Seq.index v 1 == Seq.index w 1);
    assert (Seq.index v 2 == Seq.index w 2);
    assert (Seq.index v 3 == Seq.index w 3);
    assert (Seq.index v (4 + rl) == Seq.index w (4 + rl));
    assert (Seq.index v (5 + rl) == Seq.index w (5 + rl))

inline_for_extraction
let u8_to_sz (x: U8.t) : r: SZ.t { SZ.v r == U8.v x } =
  SZ.uint16_to_sizet (Cast.uint8_to_uint16 x)

(** Whether [src[off .. off+len)] is the contents of a DER INTEGER that
    [C.der_integer_32] accepts. *)
fn der_integer_ok (src: array U8.t) (off: SZ.t) (len: SZ.t)
  requires pts_to src 'v ** pure (SZ.v off + SZ.v len <= Seq.length 'v)
  returns b: bool
  ensures pts_to src 'v **
          pure (b == Some? (C.der_integer_32 (CL.raw_slice 'v (SZ.v off) (SZ.v off + SZ.v len))))
{
  A.pts_to_len src;
  if (SZ.eq len 0sz || SZ.gt len 33sz) {
    false
  } else {
    let b0 = src.(off);
    if (U8.gte b0 0x80uy) {
      false
    } else if (SZ.gt len 1sz && b0 = 0uy) {
      let b1 = src.(SZ.add off 1sz);
      not (U8.lt b1 0x80uy)
    } else {
      true
    }
  }
}

fn der_int_byte_at (src: array U8.t) (off: SZ.t) (len: SZ.t) (k: SZ.t)
  requires pts_to src 'v **
           pure (SZ.v off + SZ.v len <= Seq.length 'v /\ SZ.v len <= 33 /\ SZ.v k < 32)
  returns x: U8.t
  ensures pts_to src 'v ** pure (x == der_int_byte 'v (SZ.v off) (SZ.v len) (SZ.v k))
{
  A.pts_to_len src;
  if (SZ.lt (SZ.add k len) 32sz) {
    0uy
  } else {
    SZ.fits_lte (SZ.v off + (SZ.v len + SZ.v k - 32)) (Seq.length 'v);
    src.(SZ.add off (SZ.sub (SZ.add len k) 32sz))
  }
}

(** [out] := the 32-byte big-endian value of the INTEGER contents
    [src[off .. off+len)]: left-padded with zeros, or with its leading zero
    byte dropped when [len = 33]. *)
fn der_integer_load (src: array U8.t) (off: SZ.t) (len: SZ.t) (out: array U8.t)
  requires pts_to src 'v ** pts_to out 'o **
           pure (SZ.v off + SZ.v len <= Seq.length 'v /\ 1 <= SZ.v len /\ SZ.v len <= 33 /\
                 Seq.length 'o == 32)
  ensures exists* o. pts_to src 'v ** pts_to out o **
          pure (Seq.length o == 32 /\
                (forall (k: nat). k < 32 ==>
                   Seq.index o k == der_int_byte 'v (SZ.v off) (SZ.v len) k))
{
  A.pts_to_len src;
  A.pts_to_len out;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 32sz)
  invariant exists* (vi: SZ.t) (o: Seq.seq U8.t).
    pts_to i vi ** pts_to out o ** pts_to src 'v **
    pure (SZ.v vi <= 32 /\ Seq.length o == 32 /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index o k == der_int_byte 'v (SZ.v off) (SZ.v len) k))
  decreases (32 - SZ.v (!i))
  {
    let vi = !i;
    let x = der_int_byte_at src off len vi;
    out.(vi) <- x;
    i := SZ.add vi 1sz;
  };
}

#push-options "--z3rlimit 40"
fn ecdsa_signature_der_decode
  (sg: array U8.t)
  (sg_len: SZ.t)
  (r: array U8.t)
  (s: array U8.t)
  requires pts_to sg 'sg_bytes **
           pts_to r 'old_r **
           pts_to s 'old_s **
           pure (SZ.v sg_len <= B.length 'sg_bytes /\
                 B.length 'old_r == 32 /\ B.length 'old_s == 32)
  returns ok: bool
  ensures exists* r_bytes s_bytes.
          pts_to sg 'sg_bytes **
          pts_to r r_bytes **
          pts_to s s_bytes **
          pure (B.length r_bytes == 32 /\ B.length s_bytes == 32 /\
                (match C.ecdsa_signature_der_decode (CL.raw_slice 'sg_bytes 0 (SZ.v sg_len)) with
                 | Some (er, es) -> ok /\ r_bytes == er /\ s_bytes == es
                 | None -> ok == false))
{
  A.pts_to_len sg;
  let v = Ghost.hide (CL.raw_slice 'sg_bytes 0 (SZ.v sg_len));
  if (SZ.lt sg_len 8sz || SZ.gt sg_len 72sz) {
    false
  } else {
    let b0 = sg.(0sz);
    let b1 = sg.(1sz);
    let b2 = sg.(2sz);
    let rl = u8_to_sz sg.(3sz);
    if (b0 <> 0x30uy || u8_to_sz b1 <> SZ.sub sg_len 2sz || b2 <> 0x02uy) {
      false
    } else if (SZ.gt (SZ.add 6sz rl) sg_len) {
      false
    } else {
      let t = sg.(SZ.add 4sz rl);
      let sl = u8_to_sz sg.(SZ.add 5sz rl);
      if (t <> 0x02uy || SZ.add (SZ.add 6sz rl) sl <> sg_len) {
        false
      } else {
        let soff = SZ.add 6sz rl;
        let rok = der_integer_ok sg 4sz rl;
        let sok = der_integer_ok sg soff sl;
        if (rok && sok) {
          der_integer_load sg 4sz rl r;
          der_integer_load sg soff sl s;
          with vr. assert (pts_to r vr);
          with vs. assert (pts_to s vs);
          der_decode_some 'sg_bytes (SZ.v sg_len) (SZ.v rl) (SZ.v sl) vr vs;
          true
        } else {
          false
        }
      }
    }
  }
}
#pop-options

fn verify_ecdsa_secp256r1_sha256
  (point: array U8.t)
  (point_len: SZ.t)
  (msg: array U8.t)
  (msg_len: SZ.t)
  (sg: array U8.t)
  (sg_len: SZ.t)
  requires pts_to point 'point_bytes **
           pts_to msg 'msg_bytes **
           pts_to sg 'sg_bytes **
           pure (SZ.v point_len <= B.length 'point_bytes /\
                 SZ.v msg_len <= B.length 'msg_bytes /\
                 SZ.v sg_len <= B.length 'sg_bytes)
  returns ok: bool
  ensures pts_to point 'point_bytes **
          pts_to msg 'msg_bytes **
          pts_to sg 'sg_bytes **
          pure (ok == C.ecdsa_secp256r1_sha256_verify
                        (CL.raw_slice 'point_bytes 0 (SZ.v point_len))
                        (CL.raw_slice 'msg_bytes 0 (SZ.v msg_len))
                        (CL.raw_slice 'sg_bytes 0 (SZ.v sg_len)))
{
  let small = below_pow2_61_sz msg_len;
  if (SZ.eq point_len 64sz && small) {
    let mut r = [| 0uy; 32sz |];
    let mut s = [| 0uy; 32sz |];
    let dec = ecdsa_signature_der_decode sg sg_len r s;
    if dec {
      with vr. assert (pts_to r vr);
      with vs. assert (pts_to s vs);
      CS.to_secret point;
      CS.to_secret msg;
      CS.to_secret r;
      CS.to_secret s;
      A.pts_to_len (CS.secret point);
      A.pts_to_len (CS.secret msg);
      assert (pure (A.length (CS.secret point) == Seq.length 'point_bytes /\
                    A.length (CS.secret msg) == Seq.length 'msg_bytes));
      let pt = Sub.sub (CS.secret point) 0sz point_len;
      let m = Sub.sub (CS.secret msg) 0sz msg_len;
      CS.classify_slice 'point_bytes 0 (SZ.v point_len);
      CS.classify_slice 'msg_bytes 0 (SZ.v msg_len);
      let ok = Hacl.P256.ecdsa_verify_sha256 m msg_len pt (CS.secret r) (CS.secret s);
      Sub.unsub_id (CS.secret msg) 0 (SZ.v msg_len) m;
      Sub.unsub_id (CS.secret point) 0 (SZ.v point_len) pt;
      CS.of_secret point;
      CS.of_secret msg;
      CS.of_secret r;
      CS.of_secret s;
      ok
    } else {
      false
    }
  } else {
    false
  }
}

fn byte_bit_length (x: U8.t)
  returns n: SZ.t
  ensures pure (SZ.v n == C.byte_bit_length x)
{
  if (U8.gte x 128uy) { 8sz }
  else if (U8.gte x 64uy) { 7sz }
  else if (U8.gte x 32uy) { 6sz }
  else if (U8.gte x 16uy) { 5sz }
  else if (U8.gte x 8uy) { 4sz }
  else if (U8.gte x 4uy) { 3sz }
  else if (U8.gte x 2uy) { 2sz }
  else if (U8.gte x 1uy) { 1sz }
  else { 0sz }
}

let rsa_pss_verify_false (n e message signature: B.bytes)
  : Lemma (requires not (C.rsa_pss_args_ok n e message signature))
          (ensures C.rsa_pss_rsae_sha256_verify n e message signature == false)
  = ()

#push-options "--z3rlimit 80"
fn verify_rsa_pss_rsae_sha256
  (modulus: array U8.t)
  (modulus_len: SZ.t)
  (exponent: array U8.t)
  (exponent_len: SZ.t)
  (msg: array U8.t)
  (msg_len: SZ.t)
  (sg: array U8.t)
  (sg_len: SZ.t)
  requires pts_to modulus 'n_bytes **
           pts_to exponent 'e_bytes **
           pts_to msg 'msg_bytes **
           pts_to sg 'sg_bytes **
           pure (SZ.v modulus_len <= B.length 'n_bytes /\
                 SZ.v exponent_len <= B.length 'e_bytes /\
                 SZ.v msg_len <= B.length 'msg_bytes /\
                 SZ.v sg_len <= B.length 'sg_bytes)
  returns ok: bool
  ensures pts_to modulus 'n_bytes **
          pts_to exponent 'e_bytes **
          pts_to msg 'msg_bytes **
          pts_to sg 'sg_bytes **
          pure (ok == C.rsa_pss_rsae_sha256_verify
                        (CL.raw_slice 'n_bytes 0 (SZ.v modulus_len))
                        (CL.raw_slice 'e_bytes 0 (SZ.v exponent_len))
                        (CL.raw_slice 'msg_bytes 0 (SZ.v msg_len))
                        (CL.raw_slice 'sg_bytes 0 (SZ.v sg_len)))
{
  let vn = Ghost.hide (CL.raw_slice 'n_bytes 0 (SZ.v modulus_len));
  let ve = Ghost.hide (CL.raw_slice 'e_bytes 0 (SZ.v exponent_len));
  let vm = Ghost.hide (CL.raw_slice 'msg_bytes 0 (SZ.v msg_len));
  let vs = Ghost.hide (CL.raw_slice 'sg_bytes 0 (SZ.v sg_len));
  let small = below_pow2_61_sz msg_len;
  if (SZ.gte modulus_len 128sz && SZ.lte modulus_len 1024sz && small &&
      SZ.gt exponent_len 0sz && SZ.lte exponent_len modulus_len &&
      SZ.eq sg_len modulus_len) {
    let n0 = modulus.(0sz);
    if (n0 = 0uy) {
      rsa_pss_verify_false vn ve vm vs;
      false
    } else {
      let bl = byte_bit_length n0;
      let mbs = SZ.add (SZ.mul 8sz (SZ.sub modulus_len 1sz)) bl;
      FStar.Math.Lemmas.small_mod (SZ.v mbs) (pow2 32);
      let mb = SZ.sizet_to_uint32 mbs;
      assert (pure (U32.v mb == C.rsa_mod_bits vn));
      C.rsa_pss_args_facts vn ve vm vs;
      CS.to_secret modulus;
      CS.to_secret exponent;
      CS.to_secret msg;
      CS.to_secret sg;
      A.pts_to_len (CS.secret modulus);
      A.pts_to_len (CS.secret exponent);
      A.pts_to_len (CS.secret msg);
      A.pts_to_len (CS.secret sg);
      let nb = Sub.sub (CS.secret modulus) 0sz modulus_len;
      let eb = Sub.sub (CS.secret exponent) 0sz exponent_len;
      let mm = Sub.sub (CS.secret msg) 0sz msg_len;
      let sb = Sub.sub (CS.secret sg) 0sz sg_len;
      CS.classify_slice 'n_bytes 0 (SZ.v modulus_len);
      CS.classify_slice 'e_bytes 0 (SZ.v exponent_len);
      CS.classify_slice 'msg_bytes 0 (SZ.v msg_len);
      CS.classify_slice 'sg_bytes 0 (SZ.v sg_len);
      let ok = Hacl.RSAPSS.verify_sha256 mb nb exponent_len eb 32sz sb msg_len mm;
      Sub.unsub_id (CS.secret sg) 0 (SZ.v sg_len) sb;
      Sub.unsub_id (CS.secret msg) 0 (SZ.v msg_len) mm;
      Sub.unsub_id (CS.secret exponent) 0 (SZ.v exponent_len) eb;
      Sub.unsub_id (CS.secret modulus) 0 (SZ.v modulus_len) nb;
      CS.of_secret modulus;
      CS.of_secret exponent;
      CS.of_secret msg;
      CS.of_secret sg;
      ok
    }
  } else {
    rsa_pss_verify_false vn ve vm vs;
    false
  }
}
#pop-options
