module TLS13.Impl.X509.Fields

(** Byte-level helpers for path validation, as transcriptions of
    [TLS13.X509.Chain]: every function returns exactly what its namesake
    there does on [cb 'b len], the first [len] bytes of its buffer. *)

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module A = Pulse.Lib.Array
module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CL = TLS13.ConnectionLog
module Cast = FStar.Int.Cast
module PK = TLS13.Impl.X509.PublicKey
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module X = TLS13.X509.Chain

inline_for_extraction noextract unfold let ( +^ ) = SZ.add
inline_for_extraction noextract unfold let ( -^ ) = SZ.sub

let cb (b:B.bytes) (len:SZ.t) : B.bytes = PK.cert_bytes b len

let ok_len (b:B.bytes) (len:SZ.t) : prop =
  SZ.v len <= B.length b /\ SZ.v len <= SZ.v PK.max_certificate_len

let cb_length (b:B.bytes) (len:SZ.t)
  : Lemma (requires SZ.v len <= B.length b)
          (ensures B.length (cb b len) == SZ.v len)
          [SMTPat (B.length (cb b len))]
  = ()

let cb_index (b:B.bytes) (len:SZ.t) (i:nat)
  : Lemma (requires SZ.v len <= B.length b /\ i < SZ.v len)
          (ensures Seq.index (cb b len) i == Seq.index b i)
          [SMTPat (Seq.index (cb b len) i)]
  = ()

let der_tlv_matches = PK.der_tlv_matches

(** {2 Bytes} *)

fn byte_is
  (c:array U8.t) (len:SZ.t) (i:SZ.t) (x:U8.t)
  requires pts_to c 'b ** pure (ok_len 'b len)
  returns r:bool
  ensures pts_to c 'b ** pure (r == X.byte_is (cb 'b len) (SZ.v i) x)
{
  if (SZ.lt i len) {
    let y = c.(i);
    (y = x)
  } else {
    false
  }
}

(** [X.range_eq] within one buffer. *)
fn range_eq_self
  (c:array U8.t) (len:SZ.t) (a0 a1 b0 b1:SZ.t)
  requires pts_to c 'b **
           pure (ok_len 'b len /\ SZ.v a1 <= SZ.v len /\ SZ.v b1 <= SZ.v len)
  returns r:bool
  ensures pts_to c 'b **
          pure (r == X.range_eq (cb 'b len) (SZ.v a0) (SZ.v a1) (cb 'b len) (SZ.v b0) (SZ.v b1))
{
  if (SZ.lte a0 a1 && SZ.lte b0 b1 && (a1 -^ a0) = (b1 -^ b0)) {
    let n = a1 -^ a0;
    let mut i = 0sz;
    let mut ok = true;
    while (let vi = !i; SZ.lt vi n)
    invariant exists* (vi:SZ.t) (vok:bool).
      pts_to i vi ** pts_to ok vok ** pts_to c 'b **
      pure (SZ.v vi <= SZ.v n /\
            X.same_bytes (cb 'b len) (SZ.v a0) (cb 'b len) (SZ.v b0) (SZ.v n) ==
            (vok && X.same_bytes (cb 'b len) (SZ.v a0 + SZ.v vi) (cb 'b len)
                      (SZ.v b0 + SZ.v vi) (SZ.v n - SZ.v vi)))
    decreases (SZ.v n - SZ.v (!i))
    {
      let vi = !i;
      let x = c.(a0 +^ vi);
      let y = c.(b0 +^ vi);
      if (x = y) {
        i := vi +^ 1sz;
      } else {
        ok := false;
        i := n;
      }
    };
    !ok
  } else {
    false
  }
}

(** [X.range_eq] across two buffers. *)
fn range_eq2
  (c:array U8.t) (len:SZ.t) (a0 a1:SZ.t)
  (d:array U8.t) (dlen:SZ.t) (b0 b1:SZ.t)
  requires pts_to c 'b ** pts_to d 'e **
           pure (ok_len 'b len /\ SZ.v a1 <= SZ.v len /\
                 SZ.v dlen <= B.length 'e /\ SZ.v b1 <= SZ.v dlen)
  returns r:bool
  ensures pts_to c 'b ** pts_to d 'e **
          pure (r == X.range_eq (cb 'b len) (SZ.v a0) (SZ.v a1) (cb 'e dlen) (SZ.v b0) (SZ.v b1))
{
  if (SZ.lte a0 a1 && SZ.lte b0 b1 && (a1 -^ a0) = (b1 -^ b0)) {
    let n = a1 -^ a0;
    let mut i = 0sz;
    let mut ok = true;
    while (let vi = !i; SZ.lt vi n)
    invariant exists* (vi:SZ.t) (vok:bool).
      pts_to i vi ** pts_to ok vok ** pts_to c 'b ** pts_to d 'e **
      pure (SZ.v vi <= SZ.v n /\
            X.same_bytes (cb 'b len) (SZ.v a0) (cb 'e dlen) (SZ.v b0) (SZ.v n) ==
            (vok && X.same_bytes (cb 'b len) (SZ.v a0 + SZ.v vi) (cb 'e dlen)
                      (SZ.v b0 + SZ.v vi) (SZ.v n - SZ.v vi)))
    decreases (SZ.v n - SZ.v (!i))
    {
      let vi = !i;
      let x = c.(a0 +^ vi);
      let y = d.(b0 +^ vi);
      if (x = y) {
        i := vi +^ 1sz;
      } else {
        ok := false;
        i := n;
      }
    };
    !ok
  } else {
    false
  }
}

(** {2 Time} *)

fn all_digits
  (c:array U8.t) (len:SZ.t) (s e:SZ.t)
  requires pts_to c 'b ** pure (ok_len 'b len)
  returns r:bool
  ensures pts_to c 'b ** pure (r == X.all_digits (cb 'b len) (SZ.v s) (SZ.v e))
{
  if (SZ.gte s e) {
    true
  } else {
  let mut i = s;
  let mut ok = true;
  while (let vi = !i; SZ.lt vi e)
  invariant exists* (vi:SZ.t) (vok:bool).
    pts_to i vi ** pts_to ok vok ** pts_to c 'b **
    pure (SZ.v vi <= SZ.v e /\
          X.all_digits (cb 'b len) (SZ.v s) (SZ.v e) ==
          (vok && X.all_digits (cb 'b len) (SZ.v vi) (SZ.v e)))
  decreases (SZ.v e - SZ.v (!i))
  {
    let vi = !i;
    if (SZ.lt vi len) {
      let x = c.(vi);
      if (U8.gte x 0x30uy && U8.lte x 0x39uy) {
        i := vi +^ 1sz;
      } else {
        ok := false;
        i := e;
      }
    } else {
      ok := false;
      i := e;
    }
  };
  !ok
  }
}

inline_for_extraction
let digit64 (x:U8.t) : r:U64.t{U64.v r == X.digit x /\ U64.v r <= 9} =
  if U8.gte x 0x30uy && U8.lte x 0x39uy then Cast.uint8_to_uint64 (U8.sub x 0x30uy) else 0UL

fn dec2
  (c:array U8.t) (len:SZ.t) (s:SZ.t)
  requires pts_to c 'b ** pure (ok_len 'b len /\ SZ.v s + 2 <= SZ.v len)
  returns r:U64.t
  ensures pts_to c 'b ** pure (U64.v r == X.dec2 (cb 'b len) (SZ.v s) /\ U64.v r <= 99)
{
  let x = c.(s);
  let y = c.(s +^ 1sz);
  U64.add (U64.mul 10UL (digit64 x)) (digit64 y)
}

inline_for_extraction
let is_leap64 (y:U64.t) : r:bool{r == X.is_leap (U64.v y)} =
  (U64.rem y 4UL = 0UL && U64.rem y 100UL <> 0UL) || U64.rem y 400UL = 0UL

inline_for_extraction
let days_in_month64 (y m:U64.t) : r:U64.t{U64.v r == X.days_in_month (U64.v y) (U64.v m)} =
  if m = 2UL then (if is_leap64 y then 29UL else 28UL)
  else if m = 4UL || m = 6UL || m = 9UL || m = 11UL then 30UL
  else 31UL

inline_for_extraction
let days_before_month64 (y m:U64.t)
  : r:U64.t{U64.v r == X.days_before_month (U64.v y) (U64.v m) /\ U64.v r <= 335} =
  let base =
    if U64.lte m 1UL then 0UL else if m = 2UL then 31UL else if m = 3UL then 59UL
    else if m = 4UL then 90UL else if m = 5UL then 120UL else if m = 6UL then 151UL
    else if m = 7UL then 181UL else if m = 8UL then 212UL else if m = 9UL then 243UL
    else if m = 10UL then 273UL else if m = 11UL then 304UL else 334UL in
  if U64.gt m 2UL && is_leap64 y then U64.add base 1UL else base

inline_for_extraction
let days_before_year64 (y:U64.t{1 <= U64.v y /\ U64.v y <= 9999})
  : r:U64.t{U64.v r == X.days_before_year (U64.v y) /\ U64.v r <= 3652059} =
  let p = U64.sub y 1UL in
  U64.add (U64.sub (U64.add (U64.mul 365UL p) (U64.div p 4UL)) (U64.div p 100UL))
    (U64.div p 400UL)

type time_value = {
  t_ok: bool;
  t_val: U64.t;
}

let instant_matches (r:time_value) (y m dd h mi s:nat) : prop =
  match X.instant y m dd h mi s with
  | Some t -> r.t_ok == true /\ U64.v r.t_val == t
  | None -> r.t_ok == false

#push-options "--z3rlimit 40"
inline_for_extraction
let instant64 (y m dd h mi s:U64.t)
  : Pure time_value
    (requires U64.v y <= 9999 /\ U64.v m <= 99 /\ U64.v dd <= 99 /\
              U64.v h <= 99 /\ U64.v mi <= 99 /\ U64.v s <= 99)
    (ensures fun r -> instant_matches r (U64.v y) (U64.v m) (U64.v dd)
                        (U64.v h) (U64.v mi) (U64.v s))
  = if U64.gte y 1UL && U64.gte m 1UL && U64.lte m 12UL && U64.gte dd 1UL &&
       U64.lte dd (days_in_month64 y m) &&
       U64.lt h 24UL && U64.lt mi 60UL && U64.lt s 60UL
    then
      let days = U64.add (U64.add (days_before_year64 y) (days_before_month64 y m))
                         (U64.sub dd 1UL) in
      { t_ok = true;
        t_val = U64.add (U64.add (U64.add (U64.mul days 86400UL) (U64.mul h 3600UL))
                                 (U64.mul mi 60UL)) s }
    else { t_ok = false; t_val = 0UL }
#pop-options


let time_matches (r:time_value) (o:option nat) : prop =
  match o with
  | Some t -> r.t_ok == true /\ U64.v r.t_val == t
  | None -> r.t_ok == false

inline_for_extraction noextract
let no_time : time_value = { t_ok = false; t_val = 0UL }

(** A UTCTime ([gen = false]) or GeneralizedTime ([gen = true]) filling
    [c[0, len)]. *)
#push-options "--z3rlimit 80"
fn time_of
  (c:array U8.t) (len:SZ.t) (gen:bool)
  requires pts_to c 'b ** pure (ok_len 'b len)
  returns r:time_value
  ensures pts_to c 'b **
          pure (time_matches r (if gen then X.generalized_time (cb 'b len) else X.utc_time (cb 'b len)))
{
  if (not gen) {
    if (len = 13sz) {
      let d = all_digits c len 0sz 12sz;
      let z = byte_is c len 12sz 0x5Auy;
      if (d && z) {
        let yy = dec2 c len 0sz;
        let y = if U64.lt yy 50UL then U64.add 2000UL yy else U64.add 1900UL yy;
        let mo = dec2 c len 2sz;
        let dd = dec2 c len 4sz;
        let h = dec2 c len 6sz;
        let mi = dec2 c len 8sz;
        let sec = dec2 c len 10sz;
        instant64 y mo dd h mi sec
      } else {
        no_time
      }
    } else {
      no_time
    }
  } else {
    if (len = 15sz) {
      let d = all_digits c len 0sz 14sz;
      let z = byte_is c len 14sz 0x5Auy;
      if (d && z) {
        let y1 = dec2 c len 0sz;
        let y2 = dec2 c len 2sz;
        let y = U64.add (U64.mul 100UL y1) y2;
        let mo = dec2 c len 4sz;
        let dd = dec2 c len 6sz;
        let h = dec2 c len 8sz;
        let mi = dec2 c len 10sz;
        let sec = dec2 c len 12sz;
        instant64 y mo dd h mi sec
      } else {
        no_time
      }
    } else {
      no_time
    }
  }
}
#pop-options
