module TLS13.Impl.X509.PublicKey

(** Verified extraction of the public key from a DER certificate, against
    [TLS13.Crypto.Spec.certificate_raw_public_key]. *)

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module A = Pulse.Lib.Array
module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CL = TLS13.ConnectionLog
module Cast = FStar.Int.Cast
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8

inline_for_extraction noextract unfold let ( +^ ) = SZ.add
inline_for_extraction noextract unfold let ( -^ ) = SZ.sub
inline_for_extraction noextract unfold let ( *^ ) = SZ.mul

(* Longer certificates are rejected, which keeps every offset below 2^16. *)
inline_for_extraction noextract
let max_certificate_len : SZ.t = 0xF000sz

inline_for_extraction
let u8_to_sz (x:U8.t) : r:SZ.t{SZ.v r == U8.v x} =
  SZ.uint16_to_sizet (Cast.uint8_to_uint16 x)

let cert_bytes (b:B.bytes) (len:SZ.t) : B.bytes = CL.raw_slice b 0 (SZ.v len)

type der_range = {
  ok: bool;
  lo: SZ.t;
  hi: SZ.t;
}

inline_for_extraction noextract
let no_range : der_range = { ok = false; lo = 0sz; hi = 0sz }

let der_tlv_matches (r:der_range) (c:B.bytes) (tag:U8.t) (pos limit:nat) : prop =
  match C.der_tlv c tag pos limit with
  | Some (lo, hi) -> r.ok == true /\ SZ.v r.lo == lo /\ SZ.v r.hi == hi
  | None -> r.ok == false

#push-options "--z3rlimit 40"
fn der_tlv_impl
  (cert:array U8.t)
  (len:SZ.t)
  (tag:U8.t)
  (pos limit:SZ.t)
  requires pts_to cert 'b ** pure (SZ.v len <= B.length 'b)
  returns r:der_range
  ensures pts_to cert 'b **
          pure (der_tlv_matches r (cert_bytes 'b len) tag (SZ.v pos) (SZ.v limit))
{
  if (SZ.gt limit len || SZ.lt limit pos || SZ.lt (limit -^ pos) 2sz) {
    no_range
  } else {
    let t = cert.(pos);
    if (t <> tag) {
      no_range
    } else {
      let l0 = cert.(pos +^ 1sz);
      let rem = limit -^ (pos +^ 2sz);
      if (U8.lt l0 0x80uy) {
        let l = u8_to_sz l0;
        if (SZ.lte l rem) {
          ({ ok = true; lo = pos +^ 2sz; hi = pos +^ 2sz +^ l })
        } else {
          no_range
        }
      } else if (l0 = 0x81uy) {
        if (SZ.lt rem 1sz) {
          no_range
        } else {
          let l = u8_to_sz cert.(pos +^ 2sz);
          if (SZ.gte l 0x80sz && SZ.lte l (rem -^ 1sz)) {
            ({ ok = true; lo = pos +^ 3sz; hi = pos +^ 3sz +^ l })
          } else {
            no_range
          }
        }
      } else if (l0 = 0x82uy) {
        if (SZ.lt rem 2sz) {
          no_range
        } else {
          let h = u8_to_sz cert.(pos +^ 2sz);
          let m = u8_to_sz cert.(pos +^ 3sz);
          let l = (h *^ 256sz) +^ m;
          if (SZ.gte l 0x100sz && SZ.lte l (rem -^ 2sz)) {
            ({ ok = true; lo = pos +^ 4sz; hi = pos +^ 4sz +^ l })
          } else {
            no_range
          }
        }
      } else {
        no_range
      }
    }
  }
}
#pop-options

let spki_matches (r:der_range) (c:B.bytes) : prop =
  match C.certificate_spki c with
  | Some (lo, hi) -> r.ok == true /\ SZ.v r.lo == lo /\ SZ.v r.hi == hi
  | None -> r.ok == false

#push-options "--z3rlimit 80"
fn certificate_spki_impl
  (cert:array U8.t)
  (len:SZ.t)
  requires pts_to cert 'b **
           pure (SZ.v len <= B.length 'b /\ SZ.v len <= SZ.v max_certificate_len)
  returns r:der_range
  ensures pts_to cert 'b **
          pure (spki_matches r (cert_bytes 'b len))
{
  let outer = der_tlv_impl cert len 0x30uy 0sz len;
  if (not outer.ok || outer.hi <> len) {
    no_range
  } else {
    let tbs = der_tlv_impl cert len 0x30uy outer.lo outer.hi;
    if (not tbs.ok) {
      no_range
    } else {
      let version = der_tlv_impl cert len 0xA0uy tbs.lo tbs.hi;
      let version_end = (if version.ok then version.hi else tbs.lo);
      let serial = der_tlv_impl cert len 0x02uy version_end tbs.hi;
      if (not serial.ok) {
        no_range
      } else {
        let signature = der_tlv_impl cert len 0x30uy serial.hi tbs.hi;
        if (not signature.ok) {
          no_range
        } else {
          let issuer = der_tlv_impl cert len 0x30uy signature.hi tbs.hi;
          if (not issuer.ok) {
            no_range
          } else {
            let validity = der_tlv_impl cert len 0x30uy issuer.hi tbs.hi;
            if (not validity.ok) {
              no_range
            } else {
              let subject = der_tlv_impl cert len 0x30uy validity.hi tbs.hi;
              if (not subject.ok) {
                no_range
              } else {
                der_tlv_impl cert len 0x30uy subject.hi tbs.hi
              }
            }
          }
        }
      }
    }
  }
}
#pop-options

fn der_uint_start_impl
  (cert:array U8.t)
  (len:SZ.t)
  (s e:SZ.t)
  requires pts_to cert 'b **
           pure (SZ.v len <= B.length 'b /\ SZ.v len <= SZ.v max_certificate_len)
  returns r:der_range
  ensures pts_to cert 'b **
          pure (match C.der_uint_start (cert_bytes 'b len) (SZ.v s) (SZ.v e) with
                | Some n -> r.ok == true /\ SZ.v r.lo == n
                | None -> r.ok == false)
{
  if (SZ.gte s e || SZ.gt e len) {
    no_range
  } else {
    let b0 = cert.(s);
    if (U8.gte b0 0x80uy) {
      no_range
    } else if (b0 = 0uy && SZ.lt (s +^ 1sz) e) {
      let b1 = cert.(s +^ 1sz);
      if (U8.lt b1 0x80uy) {
        no_range
      } else {
        ({ ok = true; lo = s +^ 1sz; hi = e })
      }
    } else {
      ({ ok = true; lo = s; hi = e })
    }
  }
}

fn rsa_encryption_algorithm_impl
  (cert:array U8.t)
  (len:SZ.t)
  (s e:SZ.t)
  requires pts_to cert 'b **
           pure (SZ.v len <= B.length 'b /\ SZ.v len <= SZ.v max_certificate_len /\
                 SZ.v s <= SZ.v len)
  returns r:bool
  ensures pts_to cert 'b **
          pure (r == C.rsa_encryption_algorithm (cert_bytes 'b len) (SZ.v s) (SZ.v e))
{
  if (e = s +^ 13sz && SZ.lte e len) {
    let b0 = cert.(s);
    let b1 = cert.(s +^ 1sz);
    let b2 = cert.(s +^ 2sz);
    let b3 = cert.(s +^ 3sz);
    let b4 = cert.(s +^ 4sz);
    let b5 = cert.(s +^ 5sz);
    let b6 = cert.(s +^ 6sz);
    let b7 = cert.(s +^ 7sz);
    let b8 = cert.(s +^ 8sz);
    let b9 = cert.(s +^ 9sz);
    let b10 = cert.(s +^ 10sz);
    let b11 = cert.(s +^ 11sz);
    let b12 = cert.(s +^ 12sz);
    (b0 = 0x06uy &&
     b1 = 0x09uy &&
     b2 = 0x2Auy &&
     b3 = 0x86uy &&
     b4 = 0x48uy &&
     b5 = 0x86uy &&
     b6 = 0xF7uy &&
     b7 = 0x0Duy &&
     b8 = 0x01uy &&
     b9 = 0x01uy &&
     b10 = 0x01uy &&
     b11 = 0x05uy &&
     b12 = 0x00uy)
  } else {
    false
  }
}

fn p256_algorithm_impl
  (cert:array U8.t)
  (len:SZ.t)
  (s e:SZ.t)
  requires pts_to cert 'b **
           pure (SZ.v len <= B.length 'b /\ SZ.v len <= SZ.v max_certificate_len /\
                 SZ.v s <= SZ.v len)
  returns r:bool
  ensures pts_to cert 'b **
          pure (r == C.p256_algorithm (cert_bytes 'b len) (SZ.v s) (SZ.v e))
{
  if (e = s +^ 19sz && SZ.lte e len) {
    let b0 = cert.(s);
    let b1 = cert.(s +^ 1sz);
    let b2 = cert.(s +^ 2sz);
    let b3 = cert.(s +^ 3sz);
    let b4 = cert.(s +^ 4sz);
    let b5 = cert.(s +^ 5sz);
    let b6 = cert.(s +^ 6sz);
    let b7 = cert.(s +^ 7sz);
    let b8 = cert.(s +^ 8sz);
    let b9 = cert.(s +^ 9sz);
    let b10 = cert.(s +^ 10sz);
    let b11 = cert.(s +^ 11sz);
    let b12 = cert.(s +^ 12sz);
    let b13 = cert.(s +^ 13sz);
    let b14 = cert.(s +^ 14sz);
    let b15 = cert.(s +^ 15sz);
    let b16 = cert.(s +^ 16sz);
    let b17 = cert.(s +^ 17sz);
    let b18 = cert.(s +^ 18sz);
    (b0 = 0x06uy &&
     b1 = 0x07uy &&
     b2 = 0x2Auy &&
     b3 = 0x86uy &&
     b4 = 0x48uy &&
     b5 = 0xCEuy &&
     b6 = 0x3Duy &&
     b7 = 0x02uy &&
     b8 = 0x01uy &&
     b9 = 0x06uy &&
     b10 = 0x08uy &&
     b11 = 0x2Auy &&
     b12 = 0x86uy &&
     b13 = 0x48uy &&
     b14 = 0xCEuy &&
     b15 = 0x3Duy &&
     b16 = 0x03uy &&
     b17 = 0x01uy &&
     b18 = 0x07uy)
  } else {
    false
  }
}

fn p384_algorithm_impl
  (cert:array U8.t)
  (len:SZ.t)
  (s e:SZ.t)
  requires pts_to cert 'b **
           pure (SZ.v len <= B.length 'b /\ SZ.v len <= SZ.v max_certificate_len /\
                 SZ.v s <= SZ.v len)
  returns r:bool
  ensures pts_to cert 'b **
          pure (r == C.p384_algorithm (cert_bytes 'b len) (SZ.v s) (SZ.v e))
{
  if (e = s +^ 16sz && SZ.lte e len) {
    let b0 = cert.(s);
    let b1 = cert.(s +^ 1sz);
    let b2 = cert.(s +^ 2sz);
    let b3 = cert.(s +^ 3sz);
    let b4 = cert.(s +^ 4sz);
    let b5 = cert.(s +^ 5sz);
    let b6 = cert.(s +^ 6sz);
    let b7 = cert.(s +^ 7sz);
    let b8 = cert.(s +^ 8sz);
    let b9 = cert.(s +^ 9sz);
    let b10 = cert.(s +^ 10sz);
    let b11 = cert.(s +^ 11sz);
    let b12 = cert.(s +^ 12sz);
    let b13 = cert.(s +^ 13sz);
    let b14 = cert.(s +^ 14sz);
    let b15 = cert.(s +^ 15sz);
    (b0 = 0x06uy &&
     b1 = 0x07uy &&
     b2 = 0x2Auy &&
     b3 = 0x86uy &&
     b4 = 0x48uy &&
     b5 = 0xCEuy &&
     b6 = 0x3Duy &&
     b7 = 0x02uy &&
     b8 = 0x01uy &&
     b9 = 0x06uy &&
     b10 = 0x05uy &&
     b11 = 0x2Buy &&
     b12 = 0x81uy &&
     b13 = 0x04uy &&
     b14 = 0x00uy &&
     b15 = 0x22uy)
  } else {
    false
  }
}

(** Ranges of [cert] holding a raw public key: [kind] 1 is an RSA key with
    modulus [k_lo, k_hi) and exponent [e_lo, e_hi); 2 is a P-256 point and
    3 a P-384 point [k_lo, k_hi); anything else is no key. *)
type raw_ranges = {
  kind: U8.t;
  k_lo: SZ.t;
  k_hi: SZ.t;
  e_lo: SZ.t;
  e_hi: SZ.t;
}

inline_for_extraction noextract
let no_key : raw_ranges = { kind = 0uy; k_lo = 0sz; k_hi = 0sz; e_lo = 0sz; e_hi = 0sz }

let raw_ranges_sound (r:raw_ranges) (c:B.bytes) (ss se:nat) : prop =
  (r.kind == 1uy ==>
    SZ.v r.k_lo <= SZ.v r.k_hi /\ SZ.v r.k_hi <= B.length c /\
    SZ.v r.e_lo <= SZ.v r.e_hi /\ SZ.v r.e_hi <= B.length c /\
    C.spki_raw_public_key c ss se ==
      Some (C.RawRsa
        (CL.raw_slice c (SZ.v r.k_lo) (SZ.v r.k_hi))
        (CL.raw_slice c (SZ.v r.e_lo) (SZ.v r.e_hi)))) /\
  (r.kind == 2uy ==>
    SZ.v r.k_lo <= SZ.v r.k_hi /\ SZ.v r.k_hi <= B.length c /\
    C.spki_raw_public_key c ss se ==
      Some (C.RawP256 (CL.raw_slice c (SZ.v r.k_lo) (SZ.v r.k_hi)))) /\
  (r.kind == 3uy ==>
    SZ.v r.k_lo <= SZ.v r.k_hi /\ SZ.v r.k_hi <= B.length c /\
    C.spki_raw_public_key c ss se ==
      Some (C.RawP384 (CL.raw_slice c (SZ.v r.k_lo) (SZ.v r.k_hi))))

#push-options "--z3rlimit 100"
fn spki_raw_impl
  (cert:array U8.t)
  (len:SZ.t)
  (ss se:SZ.t)
  requires pts_to cert 'b **
           pure (SZ.v len <= B.length 'b /\ SZ.v len <= SZ.v max_certificate_len /\
                 SZ.v ss <= SZ.v se /\ SZ.v se <= SZ.v len)
  returns r:raw_ranges
  ensures pts_to cert 'b **
          pure (raw_ranges_sound r (cert_bytes 'b len) (SZ.v ss) (SZ.v se))
{
  let alg = der_tlv_impl cert len 0x30uy ss se;
  if (not alg.ok) {
    no_key
  } else {
    let bits = der_tlv_impl cert len 0x03uy alg.hi se;
    if (not bits.ok || bits.hi <> se || SZ.gte bits.lo bits.hi) {
      no_key
    } else {
      let unused = cert.(bits.lo);
      if (unused <> 0x00uy) {
        no_key
      } else {
        let is_rsa = rsa_encryption_algorithm_impl cert len alg.lo alg.hi;
        if is_rsa {
          let rk = der_tlv_impl cert len 0x30uy (bits.lo +^ 1sz) bits.hi;
          if (not rk.ok || rk.hi <> bits.hi) {
            no_key
          } else {
            let n = der_tlv_impl cert len 0x02uy rk.lo rk.hi;
            if (not n.ok) {
              no_key
            } else {
              let e = der_tlv_impl cert len 0x02uy n.hi rk.hi;
              if (not e.ok || e.hi <> rk.hi) {
                no_key
              } else {
                let n0 = der_uint_start_impl cert len n.lo n.hi;
                let e0 = der_uint_start_impl cert len e.lo e.hi;
                if (n0.ok && e0.ok) {
                  ({ kind = 1uy; k_lo = n0.lo; k_hi = n.hi; e_lo = e0.lo; e_hi = e.hi })
                } else {
                  no_key
                }
              }
            }
          }
        } else {
          let is_p256 = p256_algorithm_impl cert len alg.lo alg.hi;
          if (is_p256 && bits.hi = bits.lo +^ 66sz) {
            let form = cert.(bits.lo +^ 1sz);
            if (form = 0x04uy) {
              ({ kind = 2uy; k_lo = bits.lo +^ 2sz; k_hi = bits.hi; e_lo = 0sz; e_hi = 0sz })
            } else {
              no_key
            }
          } else {
            let is_p384 = p384_algorithm_impl cert len alg.lo alg.hi;
            if (not is_p256 && is_p384 && bits.hi = bits.lo +^ 98sz) {
              let form = cert.(bits.lo +^ 1sz);
              if (form = 0x04uy) {
                ({ kind = 3uy; k_lo = bits.lo +^ 2sz; k_hi = bits.hi; e_lo = 0sz; e_hi = 0sz })
              } else {
                no_key
              }
            } else {
              no_key
            }
          }
        }
      }
    }
  }
}
#pop-options

let copy_range_fits (lo n:SZ.t)
  : Lemma (requires SZ.v lo + SZ.v n <= SZ.v max_certificate_len \/ SZ.fits (SZ.v lo + SZ.v n))
          (ensures SZ.fits (SZ.v lo + SZ.v n))
  = if SZ.v lo + SZ.v n <= SZ.v max_certificate_len then SZ.fits_at_least_16 (SZ.v lo + SZ.v n)

fn copy_range
  (src:array U8.t)
  (lo n:SZ.t)
  (dst:array U8.t)
  (dst_len:SZ.t)
  requires pts_to src 's **
           pts_to dst 'd **
           pure (SZ.v lo + SZ.v n <= B.length 's /\
                 (SZ.v lo + SZ.v n <= SZ.v max_certificate_len \/ SZ.fits (SZ.v lo + SZ.v n)) /\
                 SZ.v n <= SZ.v dst_len /\
                 B.length 'd == SZ.v dst_len)
  ensures exists* d.
          pts_to src 's **
          pts_to dst d **
          pure (B.length d == SZ.v dst_len /\
                CL.raw_slice d 0 (SZ.v n) == CL.raw_slice 's (SZ.v lo) (SZ.v lo + SZ.v n))
{
  A.pts_to_len src;
  A.pts_to_len dst;
  copy_range_fits lo n;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi:SZ.t) (d:Seq.seq U8.t).
    pts_to i vi ** pts_to dst d ** pts_to src 's **
    pure (SZ.v vi <= SZ.v n /\ Seq.length d == SZ.v dst_len /\
          (forall (k:nat). k < SZ.v vi ==> Seq.index d k == Seq.index 's (SZ.v lo + k)))
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    let x = src.(lo +^ vi);
    dst.(vi) <- x;
    i := vi +^ 1sz;
  };
  with d. assert (pts_to dst d);
  assert (pure (Seq.equal (Seq.slice d 0 (SZ.v n)) (Seq.slice 's (SZ.v lo) (SZ.v lo + SZ.v n))));
}

(** The certificate's public key, copied out in the raw form the verifiers in
    [TLS13.Crypto] take: 1 for an RSA key (modulus in [key[0 .. lens[0])],
    exponent in [exponent[0 .. lens[1])]), 2 for a P-256 point and 3 for a
    P-384 point (in [key[0 .. lens[0])]), 0 for no usable key (including one too large for
    the buffers). *)
#push-options "--z3rlimit 80"
fn certificate_raw_public_key
  (certificate:array U8.t)
  (certificate_len:SZ.t)
  (key:array U8.t)
  (key_capacity:SZ.t)
  (exponent:array U8.t)
  (exponent_capacity:SZ.t)
  (lens:array SZ.t)
  requires pts_to certificate 'certificate_bytes **
           pts_to key 'old_key **
           pts_to exponent 'old_exponent **
           pts_to lens 'old_lens **
           pure (SZ.v certificate_len <= B.length 'certificate_bytes /\
                 B.length 'old_key == SZ.v key_capacity /\
                 B.length 'old_exponent == SZ.v exponent_capacity /\
                 Seq.length 'old_lens == 2)
  returns kind:U8.t
  ensures exists* key_bytes exponent_bytes lens_values.
          pts_to certificate 'certificate_bytes **
          pts_to key key_bytes **
          pts_to exponent exponent_bytes **
          pts_to lens lens_values **
          pure (B.length key_bytes == SZ.v key_capacity /\
                B.length exponent_bytes == SZ.v exponent_capacity /\
                Seq.length lens_values == 2 /\
                SZ.v (Seq.index lens_values 0) <= SZ.v key_capacity /\
                SZ.v (Seq.index lens_values 1) <= SZ.v exponent_capacity /\
                (kind == 1uy ==>
                  C.certificate_raw_public_key
                    (CL.raw_slice 'certificate_bytes 0 (SZ.v certificate_len)) ==
                  Some (C.RawRsa
                    (CL.raw_slice key_bytes 0 (SZ.v (Seq.index lens_values 0)))
                    (CL.raw_slice exponent_bytes 0 (SZ.v (Seq.index lens_values 1))))) /\
                (kind == 2uy ==>
                  C.certificate_raw_public_key
                    (CL.raw_slice 'certificate_bytes 0 (SZ.v certificate_len)) ==
                  Some (C.RawP256
                    (CL.raw_slice key_bytes 0 (SZ.v (Seq.index lens_values 0))))) /\
                (kind == 3uy ==>
                  C.certificate_raw_public_key
                    (CL.raw_slice 'certificate_bytes 0 (SZ.v certificate_len)) ==
                  Some (C.RawP384
                    (CL.raw_slice key_bytes 0 (SZ.v (Seq.index lens_values 0))))))
{
  A.pts_to_len lens;
  lens.(0sz) <- 0sz;
  lens.(1sz) <- 0sz;
  if (SZ.gt certificate_len max_certificate_len) {
    0uy
  } else {
    let spki = certificate_spki_impl certificate certificate_len;
    if (not spki.ok) {
      0uy
    } else {
      let raw = spki_raw_impl certificate certificate_len spki.lo spki.hi;
      if (raw.kind = 1uy &&
          SZ.lte (raw.k_hi -^ raw.k_lo) key_capacity &&
          SZ.lte (raw.e_hi -^ raw.e_lo) exponent_capacity) {
        copy_range certificate raw.k_lo (raw.k_hi -^ raw.k_lo) key key_capacity;
        copy_range certificate raw.e_lo (raw.e_hi -^ raw.e_lo) exponent exponent_capacity;
        lens.(0sz) <- raw.k_hi -^ raw.k_lo;
        lens.(1sz) <- raw.e_hi -^ raw.e_lo;
        1uy
      } else if (raw.kind = 2uy && SZ.lte (raw.k_hi -^ raw.k_lo) key_capacity) {
        copy_range certificate raw.k_lo (raw.k_hi -^ raw.k_lo) key key_capacity;
        lens.(0sz) <- raw.k_hi -^ raw.k_lo;
        2uy
      } else if (raw.kind = 3uy && SZ.lte (raw.k_hi -^ raw.k_lo) key_capacity) {
        copy_range certificate raw.k_lo (raw.k_hi -^ raw.k_lo) key key_capacity;
        lens.(0sz) <- raw.k_hi -^ raw.k_lo;
        3uy
      } else {
        0uy
      }
    }
  }
}
#pop-options
