module TLS13.Impl.ServerCredentials

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module A = Pulse.Lib.Array
module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CL = TLS13.ConnectionLog
module Cr = TLS13.Crypto
module CS = TLS13.Spec.StateMachine
module CV = TLS13.Impl.Client.CertificateVerify
module Cast = FStar.Int.Cast
module PK = TLS13.Impl.X509.PublicKey
module Seq = FStar.Seq
module SZ = FStar.SizeT
module T = TLS13.Types
module U16 = FStar.UInt16
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec

inline_for_extraction noextract unfold let ( +^ ) = SZ.add
inline_for_extraction noextract unfold let ( -^ ) = SZ.sub

(* Large enough for any modulus [C.rsa_modulus_ok] accepts. *)
inline_for_extraction noextract
let raw_key_capacity : SZ.t = 1024sz

(** {2 The credential} *)

noeq
type server_credentials = {
  chain: V.vec U8.t;
  chain_len: SZ.t;
  secret: V.vec U8.t;
  secret_len: SZ.t;
  kind: U8.t;
}

(* [kind] is the certificate key's algorithm, as numbered by
   [PK.certificate_raw_public_key]: 1 for RSA, 2 for P-256. *)
let kind_ok (kind:U8.t) (chain:B.bytes) : prop =
  match C.certificate_raw_public_key chain with
  | Some (C.RawRsa _ _) -> kind == 1uy
  | Some (C.RawP256 _) -> kind == 2uy
  | _ -> False

let creds_ok (c:server_credentials) (chain sb:B.bytes) : prop =
  V.is_full_vec c.chain /\
  V.is_full_vec c.secret /\
  B.length chain == SZ.v c.chain_len /\
  Seq.length sb == SZ.v c.secret_len /\
  0 < SZ.v c.secret_len /\
  SZ.v c.secret_len <= SZ.v raw_key_capacity /\
  (c.kind == 2uy ==> SZ.v c.secret_len == 32) /\
  kind_ok c.kind chain

let is_server_credentials ([@@@mkey] c:server_credentials) chain identity =
  exists* (sb:B.bytes).
    V.pts_to c.chain chain **
    V.pts_to c.secret sb **
    pure (identity == chain /\ creds_ok c chain sb)

(** {2 Private keys}

    Only the location of the private scalar or exponent is extracted, and only
    memory safety is proved: a key that is malformed, of the wrong algorithm
    or not the certificate's makes signatures that fail the check in
    [sign_certificate_verify]. *)

inline_for_extraction noextract
let max_private_key_len : SZ.t = PK.max_certificate_len

let range_in (r:PK.der_range) (len:SZ.t) : prop =
  r.PK.ok ==> SZ.v r.PK.lo <= SZ.v r.PK.hi /\ SZ.v r.PK.hi <= SZ.v len

(* The content of the [RSAPrivateKey] or [ECPrivateKey] SEQUENCE: either the
   whole key, or the [privateKey] OCTET STRING of a PKCS#8 [PrivateKeyInfo]
   (recognized by the [AlgorithmIdentifier] SEQUENCE after its version). *)
#push-options "--z3rlimit 40"
fn key_structure (key:array U8.t) (len:SZ.t)
  requires pts_to key 'b ** pure (SZ.v len <= B.length 'b)
  returns r:PK.der_range
  ensures pts_to key 'b ** pure (range_in r len)
{
  let top = PK.der_tlv_impl key len 0x30uy 0sz len;
  if (not top.PK.ok) {
    PK.no_range
  } else {
    let ver = PK.der_tlv_impl key len 0x02uy top.PK.lo top.PK.hi;
    if (not ver.PK.ok || not (SZ.lt ver.PK.hi top.PK.hi)) {
      top
    } else {
      let t = key.(ver.PK.hi);
      if (t <> 0x30uy) {
        top
      } else {
        let alg = PK.der_tlv_impl key len 0x30uy ver.PK.hi top.PK.hi;
        if (not alg.PK.ok) {
          PK.no_range
        } else {
          let oct = PK.der_tlv_impl key len 0x04uy alg.PK.hi top.PK.hi;
          if (not oct.PK.ok) {
            PK.no_range
          } else {
            PK.der_tlv_impl key len 0x30uy oct.PK.lo oct.PK.hi
          }
        }
      }
    }
  }
}
#pop-options

let secret_in (r:PK.der_range) (len:SZ.t) (kind:U8.t) : prop =
  r.PK.ok ==>
    SZ.v r.PK.lo < SZ.v r.PK.hi /\ SZ.v r.PK.hi <= SZ.v len /\
    (kind <> 1uy ==> SZ.v r.PK.hi - SZ.v r.PK.lo == 32)

(* The private exponent [d] of an [RSAPrivateKey] (kind 1, as a minimal
   unsigned big-endian integer), or the 32-byte [privateKey] of an
   [ECPrivateKey]. *)
#push-options "--z3rlimit 60"
fn private_key_secret (key:array U8.t) (len:SZ.t) (kind:U8.t)
  requires pts_to key 'b **
           pure (SZ.v len <= B.length 'b /\ SZ.v len <= SZ.v max_private_key_len)
  returns r:PK.der_range
  ensures pts_to key 'b ** pure (secret_in r len kind)
{
  let s = key_structure key len;
  if (not s.PK.ok) {
    PK.no_range
  } else {
    let ver = PK.der_tlv_impl key len 0x02uy s.PK.lo s.PK.hi;
    if (not ver.PK.ok) {
      PK.no_range
    } else if (kind = 1uy) {
      let n = PK.der_tlv_impl key len 0x02uy ver.PK.hi s.PK.hi;
      if (not n.PK.ok) {
        PK.no_range
      } else {
        let e = PK.der_tlv_impl key len 0x02uy n.PK.hi s.PK.hi;
        if (not e.PK.ok) {
          PK.no_range
        } else {
          let d = PK.der_tlv_impl key len 0x02uy e.PK.hi s.PK.hi;
          if (not d.PK.ok) {
            PK.no_range
          } else {
            let st = PK.der_uint_start_impl key len d.PK.lo d.PK.hi;
            if (not st.PK.ok) {
              PK.no_range
            } else {
              ({ PK.ok = true; PK.lo = st.PK.lo; PK.hi = d.PK.hi })
            }
          }
        }
      }
    } else {
      let oct = PK.der_tlv_impl key len 0x04uy ver.PK.hi s.PK.hi;
      if (oct.PK.ok && SZ.eq (oct.PK.hi -^ oct.PK.lo) 32sz) {
        oct
      } else {
        PK.no_range
      }
    }
  }
}
#pop-options

(** {2 Construction and destruction} *)

fn copy_all (src:array U8.t) (n:SZ.t) (dst:V.vec U8.t)
  requires pts_to src 's **
           V.pts_to dst 'd **
           pure (B.length 's == SZ.v n /\ V.length dst == SZ.v n)
  ensures pts_to src 's ** V.pts_to dst 's
{
  V.pts_to_len dst;
  V.to_array_pts_to dst;
  PK.copy_range src 0sz n (V.vec_to_array dst) n;
  with d. assert (pts_to (V.vec_to_array dst) d);
  assert (pure (Seq.equal d 's));
  V.to_vec_pts_to dst;
}

let raw_slice_full (b:B.bytes) (n:nat)
  : Lemma (requires B.length b == n) (ensures CL.raw_slice b 0 n == b)
  = assert (Seq.equal (Seq.slice b 0 n) b)

fn server_credentials_new
  (certificate_chain:array U8.t)
  (certificate_chain_len:SZ.t)
  (private_key:array U8.t)
  (private_key_len:SZ.t)
  requires pts_to certificate_chain 'certificate_chain_bytes **
           pts_to private_key 'private_key_bytes **
           pure (B.length 'certificate_chain_bytes == SZ.v certificate_chain_len /\
                 B.length 'private_key_bytes == SZ.v private_key_len)
  returns result: option server_credentials
  ensures exists* credential_identity.
          pts_to certificate_chain 'certificate_chain_bytes **
          pts_to private_key 'private_key_bytes **
          (match result with
           | Some creds ->
             is_server_credentials
               creds
               (Ghost.reveal 'certificate_chain_bytes)
               credential_identity
           | None -> emp)
{
  raw_slice_full 'certificate_chain_bytes (SZ.v certificate_chain_len);
  let mut pk = [| 0uy; raw_key_capacity |];
  let mut exponent = [| 0uy; raw_key_capacity |];
  let mut lens = [| 0sz; 2sz |];
  let kind =
    PK.certificate_raw_public_key
      certificate_chain certificate_chain_len
      pk raw_key_capacity exponent raw_key_capacity lens;
  if ((kind = 1uy || kind = 2uy) &&
      SZ.gt certificate_chain_len 0sz &&
      SZ.lte private_key_len max_private_key_len) {
    let r = private_key_secret private_key private_key_len kind;
    if (r.PK.ok && SZ.lte (r.PK.hi -^ r.PK.lo) raw_key_capacity) {
      let secret_len = r.PK.hi -^ r.PK.lo;
      let secret = V.alloc 0uy secret_len;
      V.to_array_pts_to secret;
      PK.copy_range private_key r.PK.lo secret_len (V.vec_to_array secret) secret_len;
      with sb. assert (pts_to (V.vec_to_array secret) sb);
      V.to_vec_pts_to secret;
      let chain = V.alloc 0uy certificate_chain_len;
      copy_all certificate_chain certificate_chain_len chain;
      let creds = { chain; chain_len = certificate_chain_len; secret; secret_len; kind };
      rewrite (V.pts_to chain 'certificate_chain_bytes)
           as (V.pts_to creds.chain 'certificate_chain_bytes);
      rewrite (V.pts_to secret sb) as (V.pts_to creds.secret sb);
      assert (pure (creds_ok creds 'certificate_chain_bytes sb));
      fold (is_server_credentials creds
              'certificate_chain_bytes 'certificate_chain_bytes);
      Some creds
    } else {
      let none = None #server_credentials;
      rewrite emp as (match none with
                      | Some creds -> is_server_credentials creds 'certificate_chain_bytes 'certificate_chain_bytes
                      | None -> emp);
      none
    }
  } else {
    let none = None #server_credentials;
    rewrite emp as (match none with
                    | Some creds -> is_server_credentials creds 'certificate_chain_bytes 'certificate_chain_bytes
                    | None -> emp);
    none
  }
}

fn server_credentials_clone (creds:server_credentials)
  requires is_server_credentials creds 'certificate_chain 'credential_identity
  returns clone: server_credentials
  ensures is_server_credentials creds 'certificate_chain 'credential_identity **
          is_server_credentials clone 'certificate_chain 'credential_identity
{
  unfold (is_server_credentials creds 'certificate_chain 'credential_identity);
  with sb. assert (V.pts_to creds.secret sb);
  let chain = V.alloc 0uy creds.chain_len;
  let secret = V.alloc 0uy creds.secret_len;
  V.to_array_pts_to creds.chain;
  copy_all (V.vec_to_array creds.chain) creds.chain_len chain;
  V.to_vec_pts_to creds.chain;
  V.to_array_pts_to creds.secret;
  copy_all (V.vec_to_array creds.secret) creds.secret_len secret;
  V.to_vec_pts_to creds.secret;
  let clone = { creds with chain; secret };
  rewrite (V.pts_to chain 'certificate_chain) as (V.pts_to clone.chain 'certificate_chain);
  rewrite (V.pts_to secret sb) as (V.pts_to clone.secret sb);
  assert (pure (creds_ok clone 'certificate_chain sb));
  fold (is_server_credentials creds 'certificate_chain 'credential_identity);
  fold (is_server_credentials clone 'certificate_chain 'credential_identity);
  clone
}

(** {2 Signing} *)

(* The first byte of the minimal encoding of the big-endian 32-byte integer
   at [raw[off ..]]. *)
fn int_start (raw:array U8.t) (off:SZ.t)
  requires pts_to raw 'r **
           pure (Seq.length 'r == 64 /\ (SZ.v off == 0 \/ SZ.v off == 32))
  returns i:SZ.t
  ensures pts_to raw 'r ** pure (SZ.v i < 32)
{
  let mut i = 0sz;
  while (
    let vi = !i;
    if (SZ.lt vi 31sz) {
      let b = raw.(off +^ vi);
      (b = 0uy)
    } else {
      false
    })
  invariant exists* (vi:SZ.t).
    pts_to i vi ** pts_to raw 'r ** pure (SZ.v vi <= 31)
  decreases (31 - SZ.v (!i))
  {
    let vi = !i;
    i := vi +^ 1sz;
  };
  !i
}

(* Writes the DER INTEGER for the 32-byte integer at [raw[off ..]] at
   [out[pos ..]], returning the position after it. *)
#push-options "--z3rlimit 40"
fn write_der_int
  (raw:array U8.t)
  (off:SZ.t)
  (out:array U8.t)
  (pos:SZ.t)
  (cap:SZ.t)
  requires pts_to raw 'r **
           pts_to out 'o **
           pure (Seq.length 'r == 64 /\ (SZ.v off == 0 \/ SZ.v off == 32) /\
                 B.length 'o == SZ.v cap /\ SZ.v pos + 35 <= SZ.v cap)
  returns next:SZ.t
  ensures exists* o.
          pts_to raw 'r **
          pts_to out o **
          pure (B.length o == SZ.v cap /\
                SZ.v pos + 3 <= SZ.v next /\ SZ.v next <= SZ.v pos + 35)
{
  let i = int_start raw off;
  let b = raw.(off +^ i);
  let pad = (if U8.gte b 0x80uy then 1sz else 0sz);
  let n = 32sz -^ i;
  let int_len = n +^ pad;
  out.(pos) <- 0x02uy;
  out.(pos +^ 1sz) <- Cast.uint32_to_uint8 (SZ.sizet_to_uint32 int_len);
  out.(pos +^ 2sz) <- 0uy;
  let start = pos +^ 2sz +^ pad;
  let mut j = 0sz;
  while (let vj = !j; SZ.lt vj n)
  invariant exists* (vj:SZ.t) (o:Seq.seq U8.t).
    pts_to j vj ** pts_to out o ** pts_to raw 'r **
    pure (SZ.v vj <= SZ.v n /\ Seq.length o == SZ.v cap)
  decreases (SZ.v n - SZ.v (!j))
  {
    let vj = !j;
    let x = raw.(off +^ i +^ vj);
    out.(start +^ vj) <- x;
    j := vj +^ 1sz;
  };
  start +^ n
}
#pop-options

(* An ECDSA signature [r || s] as the DER [ECDSA-Sig-Value] TLS sends
   (RFC 8446 4.2.3), at most 72 bytes. *)
fn ecdsa_der_encode (raw:array U8.t) (out:array U8.t) (cap:SZ.t)
  requires pts_to raw 'r **
           pts_to out 'o **
           pure (Seq.length 'r == 64 /\ B.length 'o == SZ.v cap /\ SZ.v cap >= 72)
  returns len:SZ.t
  ensures exists* o.
          pts_to raw 'r **
          pts_to out o **
          pure (B.length o == SZ.v cap /\ SZ.v len <= SZ.v cap)
{
  out.(0sz) <- 0x30uy;
  let p1 = write_der_int raw 0sz out 2sz cap;
  let p2 = write_der_int raw 32sz out p1 cap;
  out.(1sz) <- Cast.uint32_to_uint8 (SZ.sizet_to_uint32 (p2 -^ 2sz));
  p2
}

let signed
  (chain input:B.bytes)
  (input_len:SZ.t)
  (sg:B.bytes)
  (cap:SZ.t)
  (result:option SZ.t)
  : prop =
  SZ.v input_len <= B.length input /\
  B.length sg == SZ.v cap /\
  (match result with
   | Some signature_len ->
     SZ.v signature_len <= SZ.v cap /\
     SZ.v signature_len <= B.length sg /\
     C.verify_signature
       (C.credential_signature_scheme chain)
       chain
       (Seq.slice input 0 (SZ.v input_len))
       (Seq.slice sg 0 (SZ.v signature_len))
   | None -> True)

let checked_signed
  (chain input:B.bytes)
  (input_len:SZ.t)
  (sg:B.bytes)
  (cap len:SZ.t)
  (sch:T.signature_scheme)
  : Lemma
    (requires
      SZ.v input_len <= B.length input /\
      B.length sg == SZ.v cap /\
      SZ.v len <= SZ.v cap /\
      C.credential_signature_scheme chain == sch /\
      C.verify_signature sch
        (CL.raw_slice chain 0 (B.length chain))
        (CL.raw_slice input 0 (SZ.v input_len))
        (CL.raw_slice sg 0 (SZ.v len)) == true)
    (ensures signed chain input input_len sg cap (Some len))
  = raw_slice_full chain (B.length chain)

#push-options "--z3rlimit 60"
fn sign_rsa
  (chain:array U8.t)
  (chain_len:SZ.t)
  (secret:array U8.t)
  (secret_len:SZ.t)
  (input:array U8.t)
  (input_len:SZ.t)
  (signature:array U8.t)
  (signature_capacity:SZ.t)
  requires pts_to chain 'chain_bytes **
           pts_to secret 'secret_bytes **
           pts_to input 'input_bytes **
           pts_to signature 'old_signature **
           pure (B.length 'chain_bytes == SZ.v chain_len /\
                 B.length 'secret_bytes == SZ.v secret_len /\
                 SZ.v input_len <= B.length 'input_bytes /\
                 B.length 'old_signature == SZ.v signature_capacity /\
                 C.credential_signature_scheme 'chain_bytes == T.Rsa_pss_rsae_sha256)
  returns result: option SZ.t
  ensures exists* signature_bytes.
          pts_to chain 'chain_bytes **
          pts_to secret 'secret_bytes **
          pts_to input 'input_bytes **
          pts_to signature signature_bytes **
          pure (signed 'chain_bytes 'input_bytes input_len
                  signature_bytes signature_capacity result)
{
  let mut pk = [| 0uy; raw_key_capacity |];
  let mut exponent = [| 0uy; raw_key_capacity |];
  let mut lens = [| 0sz; 2sz |];
  let mut salt = [| 0uy; 32sz |];
  let k =
    PK.certificate_raw_public_key
      chain chain_len pk raw_key_capacity exponent raw_key_capacity lens;
  let modulus_len = lens.(0sz);
  if (k = 1uy && SZ.lte modulus_len signature_capacity) {
    let got = Cr.random_bytes salt 32sz;
    if got {
      let ok =
        Cr.sign_rsa_pss_rsae_sha256
          pk modulus_len secret secret_len salt input input_len signature;
      if ok {
        let valid =
          CV.verify_peer_signature
            chain chain_len 0x0804us (Ghost.hide T.Rsa_pss_rsae_sha256)
            input input_len signature modulus_len;
        if valid {
          with sg. assert (pts_to signature sg);
          checked_signed 'chain_bytes 'input_bytes input_len sg
            signature_capacity modulus_len T.Rsa_pss_rsae_sha256;
          Some modulus_len
        } else {
          None #SZ.t
        }
      } else {
        None #SZ.t
      }
    } else {
      None #SZ.t
    }
  } else {
    None #SZ.t
  }
}
#pop-options

#push-options "--z3rlimit 60"
fn sign_p256
  (chain:array U8.t)
  (chain_len:SZ.t)
  (secret:array U8.t)
  (input:array U8.t)
  (input_len:SZ.t)
  (signature:array U8.t)
  (signature_capacity:SZ.t)
  requires pts_to chain 'chain_bytes **
           pts_to secret 'secret_bytes **
           pts_to input 'input_bytes **
           pts_to signature 'old_signature **
           pure (B.length 'chain_bytes == SZ.v chain_len /\
                 B.length 'secret_bytes == 32 /\
                 SZ.v input_len <= B.length 'input_bytes /\
                 B.length 'old_signature == SZ.v signature_capacity /\
                 C.credential_signature_scheme 'chain_bytes == T.Ecdsa_secp256r1_sha256)
  returns result: option SZ.t
  ensures exists* signature_bytes.
          pts_to chain 'chain_bytes **
          pts_to secret 'secret_bytes **
          pts_to input 'input_bytes **
          pts_to signature signature_bytes **
          pure (signed 'chain_bytes 'input_bytes input_len
                  signature_bytes signature_capacity result)
{
  let mut nonce = [| 0uy; 32sz |];
  let mut raw = [| 0uy; 64sz |];
  if (SZ.gte signature_capacity 72sz) {
    let got = Cr.random_bytes nonce 32sz;
    if got {
      let ok = Cr.sign_ecdsa_secp256r1_sha256 secret nonce input input_len raw;
      if ok {
        let len = ecdsa_der_encode raw signature signature_capacity;
        let valid =
          CV.verify_peer_signature
            chain chain_len 0x0403us (Ghost.hide T.Ecdsa_secp256r1_sha256)
            input input_len signature len;
        if valid {
          with sg. assert (pts_to signature sg);
          checked_signed 'chain_bytes 'input_bytes input_len sg
            signature_capacity len T.Ecdsa_secp256r1_sha256;
          Some len
        } else {
          None #SZ.t
        }
      } else {
        None #SZ.t
      }
    } else {
      None #SZ.t
    }
  } else {
    None #SZ.t
  }
}
#pop-options

#push-options "--z3rlimit 40"
fn sign_with
  (c:server_credentials)
  (chain:array U8.t)
  (secret:array U8.t)
  (input:array U8.t)
  (input_len:SZ.t)
  (signature:array U8.t)
  (signature_capacity:SZ.t)
  requires pts_to chain 'chain_bytes **
           pts_to secret 'secret_bytes **
           pts_to input 'input_bytes **
           pts_to signature 'old_signature **
           pure (creds_ok c 'chain_bytes 'secret_bytes /\
                 SZ.v input_len <= B.length 'input_bytes /\
                 B.length 'old_signature == SZ.v signature_capacity)
  returns result: option SZ.t
  ensures exists* signature_bytes.
          pts_to chain 'chain_bytes **
          pts_to secret 'secret_bytes **
          pts_to input 'input_bytes **
          pts_to signature signature_bytes **
          pure (signed 'chain_bytes 'input_bytes input_len
                  signature_bytes signature_capacity result)
{
  C.lemma_credential_signature_scheme_def 'chain_bytes;
  if (c.kind = 1uy) {
    sign_rsa chain c.chain_len secret c.secret_len input input_len
      signature signature_capacity
  } else {
    sign_p256 chain c.chain_len secret input input_len
      signature signature_capacity
  }
}
#pop-options

fn sign_certificate_verify
  (creds:server_credentials)
  (input:array U8.t)
  (input_len:SZ.t)
  (signature:array U8.t)
  (signature_capacity:SZ.t)
  requires is_server_credentials creds 'certificate_chain 'credential_identity **
           pts_to input 'input_bytes **
           pts_to signature 'old_signature **
           pure (SZ.v input_len <= B.length 'input_bytes /\
                 B.length 'old_signature == SZ.v signature_capacity)
  returns result: option SZ.t
  ensures exists* signature_bytes.
          is_server_credentials creds 'certificate_chain 'credential_identity **
          pts_to input 'input_bytes **
          pts_to signature signature_bytes **
          pure (SZ.v input_len <= B.length (Ghost.reveal 'input_bytes) /\
                B.length signature_bytes == SZ.v signature_capacity /\
                (match result with
                 | Some signature_len ->
                   SZ.v signature_len <= SZ.v signature_capacity /\
                   SZ.v signature_len <= B.length signature_bytes /\
                   C.verify_signature
                     (C.credential_signature_scheme
                       (Ghost.reveal 'credential_identity))
                     (Ghost.reveal 'credential_identity)
                     (Seq.slice (Ghost.reveal 'input_bytes) 0 (SZ.v input_len))
                     (Seq.slice signature_bytes 0 (SZ.v signature_len))
                 | None -> True))
{
  unfold (is_server_credentials creds 'certificate_chain 'credential_identity);
  V.to_array_pts_to creds.chain;
  V.to_array_pts_to creds.secret;
  let result =
    sign_with creds (V.vec_to_array creds.chain) (V.vec_to_array creds.secret)
      input input_len signature signature_capacity;
  V.to_vec_pts_to creds.chain;
  V.to_vec_pts_to creds.secret;
  fold (is_server_credentials creds 'certificate_chain 'credential_identity);
  result
}

fn server_credential_signature_scheme (creds:server_credentials)
  requires is_server_credentials creds 'certificate_chain 'credential_identity
  returns code: U16.t
  ensures is_server_credentials creds 'certificate_chain 'credential_identity **
          pure ((U16.v code == 0x0804 /\
                 C.credential_signature_scheme
                   (Ghost.reveal 'credential_identity) ==
                   T.Rsa_pss_rsae_sha256) \/
                (U16.v code == 0x0403 /\
                 C.credential_signature_scheme
                   (Ghost.reveal 'credential_identity) ==
                   T.Ecdsa_secp256r1_sha256))
{
  unfold (is_server_credentials creds 'certificate_chain 'credential_identity);
  C.lemma_credential_signature_scheme_def 'credential_identity;
  fold (is_server_credentials creds 'certificate_chain 'credential_identity);
  if (creds.kind = 1uy) { 0x0804us } else { 0x0403us }
}

fn copy_server_certificate_chain
  (creds:server_credentials)
  (out:array U8.t)
  (out_capacity:SZ.t)
  requires is_server_credentials creds 'certificate_chain 'credential_identity **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_capacity)
  returns result: option SZ.t
  ensures exists* out_bytes.
          is_server_credentials creds 'certificate_chain 'credential_identity **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_capacity /\
                (match result with
                 | Some written ->
                  SZ.v written == B.length (Ghost.reveal 'certificate_chain) /\
                  SZ.v written <= SZ.v out_capacity /\
                  Seq.equal
                    (Seq.slice out_bytes 0 (SZ.v written))
                    (Ghost.reveal 'certificate_chain)
                 | None ->
                   B.length (Ghost.reveal 'certificate_chain) > SZ.v out_capacity))
{
  unfold (is_server_credentials creds 'certificate_chain 'credential_identity);
  let n = creds.chain_len;
  if (SZ.lte n out_capacity) {
    V.to_array_pts_to creds.chain;
    PK.copy_range (V.vec_to_array creds.chain) 0sz n out out_capacity;
    V.to_vec_pts_to creds.chain;
    raw_slice_full 'certificate_chain (SZ.v n);
    fold (is_server_credentials creds 'certificate_chain 'credential_identity);
    Some n
  } else {
    fold (is_server_credentials creds 'certificate_chain 'credential_identity);
    None #SZ.t
  }
}

fn wipe (a:array U8.t) (n:SZ.t)
  requires pts_to a 's ** pure (B.length 's == SZ.v n)
  ensures exists* s'. pts_to a s' ** pure (B.length s' == SZ.v n)
{
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi:SZ.t) (s':Seq.seq U8.t).
    pts_to i vi ** pts_to a s' **
    pure (SZ.v vi <= SZ.v n /\ Seq.length s' == SZ.v n)
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    a.(vi) <- 0uy;
    i := vi +^ 1sz;
  }
}

fn server_credentials_free (creds:server_credentials)
  requires is_server_credentials creds 'certificate_chain 'credential_identity
  ensures emp
{
  unfold (is_server_credentials creds 'certificate_chain 'credential_identity);
  V.to_array_pts_to creds.secret;
  wipe (V.vec_to_array creds.secret) creds.secret_len;
  V.to_vec_pts_to creds.secret;
  V.free creds.secret;
  V.free creds.chain;
}
