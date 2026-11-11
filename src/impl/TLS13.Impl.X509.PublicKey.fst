module TLS13.Impl.X509.PublicKey

(** The DER scanning helpers the X.509 modules share.  The certificate's
    public key is read by [TLS13.Impl.X509.Key]. *)

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

