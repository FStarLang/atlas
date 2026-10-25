module TLS13.Impl.X509.Fields

(** Verified parsing of the certificate fields path validation reads, as a
    transcription of [TLS13.X509.Spec]: every function returns exactly what
    its namesake there does on [cb 'b len], the first [len] bytes of its
    buffer. *)

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
module X = TLS13.X509.Spec

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
                 ok_len 'e dlen /\ SZ.v b1 <= SZ.v dlen)
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

let der_any_matches (r:PK.der_range) (c:B.bytes) (pos limit:nat) : prop =
  match X.der_any c pos limit with
  | Some (lo, hi) -> r.ok == true /\ SZ.v r.lo == lo /\ SZ.v r.hi == hi
  | None -> r.ok == false

fn der_any
  (c:array U8.t) (len:SZ.t) (pos limit:SZ.t)
  requires pts_to c 'b ** pure (ok_len 'b len)
  returns r:PK.der_range
  ensures pts_to c 'b ** pure (der_any_matches r (cb 'b len) (SZ.v pos) (SZ.v limit))
{
  if (SZ.lt pos limit && SZ.lte limit len) {
    let tag = c.(pos);
    PK.der_tlv_impl c len tag pos limit
  } else {
    PK.no_range
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

type time_range = {
  tr_ok: bool;
  tr_val: U64.t;
  tr_end: SZ.t;
}

let time_matches (r:time_range) (c:B.bytes) (pos limit:nat) : prop =
  match X.parse_time c pos limit with
  | Some (t, e) -> r.tr_ok == true /\ U64.v r.tr_val == t /\ SZ.v r.tr_end == e
  | None -> r.tr_ok == false

inline_for_extraction noextract
let no_time : time_range = { tr_ok = false; tr_val = 0UL; tr_end = 0sz }

#push-options "--z3rlimit 80"
fn parse_time
  (c:array U8.t) (len:SZ.t) (pos limit:SZ.t)
  requires pts_to c 'b ** pure (ok_len 'b len)
  returns r:time_range
  ensures pts_to c 'b ** pure (time_matches r (cb 'b len) (SZ.v pos) (SZ.v limit))
{
  let u = PK.der_tlv_impl c len 0x17uy pos limit;
  if (u.ok) {
    let s = u.lo;
    let e = u.hi;
    if (e = s +^ 13sz) {
      let d = all_digits c len s (s +^ 12sz);
      let z = byte_is c len (s +^ 12sz) 0x5Auy;
      if (d && z) {
        let yy = dec2 c len s;
        let y = if U64.lt yy 50UL then U64.add 2000UL yy else U64.add 1900UL yy;
        let mo = dec2 c len (s +^ 2sz);
        let dd = dec2 c len (s +^ 4sz);
        let h = dec2 c len (s +^ 6sz);
        let mi = dec2 c len (s +^ 8sz);
        let sec = dec2 c len (s +^ 10sz);
        let t = instant64 y mo dd h mi sec;
        if (t.t_ok) {
          ({ tr_ok = true; tr_val = t.t_val; tr_end = e })
        } else {
          no_time
        }
      } else {
        no_time
      }
    } else {
      no_time
    }
  } else {
    let g = PK.der_tlv_impl c len 0x18uy pos limit;
    if (g.ok) {
      let s = g.lo;
      let e = g.hi;
      if (e = s +^ 15sz) {
        let d = all_digits c len s (s +^ 14sz);
        let z = byte_is c len (s +^ 14sz) 0x5Auy;
        if (d && z) {
          let y1 = dec2 c len s;
          let y2 = dec2 c len (s +^ 2sz);
          let y = U64.add (U64.mul 100UL y1) y2;
          let mo = dec2 c len (s +^ 4sz);
          let dd = dec2 c len (s +^ 6sz);
          let h = dec2 c len (s +^ 8sz);
          let mi = dec2 c len (s +^ 10sz);
          let sec = dec2 c len (s +^ 12sz);
          let t = instant64 y mo dd h mi sec;
          if (t.t_ok) {
            ({ tr_ok = true; tr_val = t.t_val; tr_end = e })
          } else {
            no_time
          }
        } else {
          no_time
        }
      } else {
        no_time
      }
    } else {
      no_time
    }
  }
}
#pop-options

(** {2 Extensions} *)

type ext_v = {
  x_ok: bool;
  x_oid_s: SZ.t;
  x_oid_e: SZ.t;
  x_crit: bool;
  x_val_s: SZ.t;
  x_val_e: SZ.t;
  x_end: SZ.t;
}

let to_ext (r:ext_v) : X.extension =
  { X.oid_s = SZ.v r.x_oid_s; X.oid_e = SZ.v r.x_oid_e; X.critical = r.x_crit;
    X.value_s = SZ.v r.x_val_s; X.value_e = SZ.v r.x_val_e; X.ext_end = SZ.v r.x_end }

let ext_matches (r:ext_v) (c:B.bytes) (pos limit:nat) : prop =
  match X.ext_at c pos limit with
  | Some x ->
    r.x_ok == true /\ to_ext r == x /\
    SZ.v r.x_oid_s <= SZ.v r.x_oid_e /\ SZ.v r.x_oid_e <= SZ.v r.x_end /\
    SZ.v r.x_val_s <= SZ.v r.x_val_e /\ SZ.v r.x_val_e <= SZ.v r.x_end /\
    SZ.v r.x_end <= limit /\ limit <= B.length c
  | None -> r.x_ok == false

inline_for_extraction noextract
let no_ext : ext_v =
  { x_ok = false; x_oid_s = 0sz; x_oid_e = 0sz; x_crit = false;
    x_val_s = 0sz; x_val_e = 0sz; x_end = 0sz }

#push-options "--z3rlimit 80"
fn ext_at
  (c:array U8.t) (len:SZ.t) (pos limit:SZ.t)
  requires pts_to c 'b ** pure (ok_len 'b len)
  returns r:ext_v
  ensures pts_to c 'b ** pure (ext_matches r (cb 'b len) (SZ.v pos) (SZ.v limit))
{
  let s = PK.der_tlv_impl c len 0x30uy pos limit;
  if (s.ok) {
    let o = PK.der_tlv_impl c len 0x06uy s.lo s.hi;
    if (o.ok) {
      let bo = PK.der_tlv_impl c len 0x01uy o.hi s.hi;
      if (bo.ok) {
        let ff = byte_is c len bo.lo 0xFFuy;
        if (bo.hi = bo.lo +^ 1sz && ff) {
          let v = PK.der_tlv_impl c len 0x04uy bo.hi s.hi;
          if (v.ok && v.hi = s.hi) {
            ({ x_ok = true; x_oid_s = o.lo; x_oid_e = o.hi; x_crit = true;
               x_val_s = v.lo; x_val_e = v.hi; x_end = s.hi })
          } else {
            no_ext
          }
        } else {
          no_ext
        }
      } else {
        let v = PK.der_tlv_impl c len 0x04uy o.hi s.hi;
        if (v.ok && v.hi = s.hi) {
          ({ x_ok = true; x_oid_s = o.lo; x_oid_e = o.hi; x_crit = false;
             x_val_s = v.lo; x_val_e = v.hi; x_end = s.hi })
        } else {
          no_ext
        }
      }
    } else {
      no_ext
    }
  } else {
    no_ext
  }
}
#pop-options

fn ext_oid_is
  (c:array U8.t) (len:SZ.t) (x:ext_v) (k:U8.t)
  requires pts_to c 'b **
           pure (ok_len 'b len /\ SZ.v x.x_oid_s <= SZ.v x.x_oid_e /\ SZ.v x.x_oid_e <= SZ.v len)
  returns r:bool
  ensures pts_to c 'b ** pure (r == X.ext_oid_is (cb 'b len) (to_ext x) k)
{
  if (x.x_oid_e -^ x.x_oid_s = 3sz) {
    let a = byte_is c len x.x_oid_s 0x55uy;
    let b = byte_is c len (x.x_oid_s +^ 1sz) 0x1Duy;
    let d = byte_is c len (x.x_oid_s +^ 2sz) k;
    (a && b && d)
  } else {
    false
  }
}

fn extensions_wf
  (c:array U8.t) (len:SZ.t) (pos limit:SZ.t)
  requires pts_to c 'b ** pure (ok_len 'b len)
  returns r:bool
  ensures pts_to c 'b ** pure (r == X.extensions_wf (cb 'b len) (SZ.v pos) (SZ.v limit))
{
  if (SZ.gte pos limit) {
    (pos = limit)
  } else {
    let mut p = pos;
    let mut ok = true;
    while (let vp = !p; SZ.lt vp limit)
    invariant exists* (vp:SZ.t) (vok:bool).
      pts_to p vp ** pts_to ok vok ** pts_to c 'b **
      pure (SZ.v vp <= SZ.v limit /\
            X.extensions_wf (cb 'b len) (SZ.v pos) (SZ.v limit) ==
            (vok && X.extensions_wf (cb 'b len) (SZ.v vp) (SZ.v limit)))
    decreases (SZ.v limit - SZ.v (!p))
    {
      let vp = !p;
      let x = ext_at c len vp limit;
      if (x.x_ok) {
        p := x.x_end;
      } else {
        ok := false;
        p := limit;
      }
    };
    !ok
  }
}

let opt_range_matches (r:PK.der_range) (o:option (nat & nat)) : prop =
  match o with
  | Some (lo, hi) -> r.ok == true /\ SZ.v r.lo == lo /\ SZ.v r.hi == hi
  | None -> r.ok == false

let find_extension_hit (c:B.bytes) (pos limit:nat) (k:U8.t) (r:ext_v)
  : Lemma (requires pos < limit /\ ext_matches r c pos limit /\ r.x_ok /\
                    X.ext_oid_is c (to_ext r) k)
          (ensures X.find_extension c pos limit k == Some (SZ.v r.x_val_s, SZ.v r.x_val_e))
  = ()

let find_extension_miss (c:B.bytes) (pos limit:nat) (k:U8.t) (r:ext_v)
  : Lemma (requires pos < limit /\ ext_matches r c pos limit /\ r.x_ok /\
                    not (X.ext_oid_is c (to_ext r) k))
          (ensures X.find_extension c pos limit k == X.find_extension c (SZ.v r.x_end) limit k)
  = ()

#push-options "--z3rlimit 40"
fn find_extension
  (c:array U8.t) (len:SZ.t) (pos limit:SZ.t) (k:U8.t)
  requires pts_to c 'b ** pure (ok_len 'b len)
  returns r:PK.der_range
  ensures pts_to c 'b **
          pure (opt_range_matches r (X.find_extension (cb 'b len) (SZ.v pos) (SZ.v limit) k) /\
                (r.ok ==> SZ.v r.lo <= SZ.v r.hi /\ SZ.v r.hi <= SZ.v len))
{
  if (SZ.gte pos limit) {
    PK.no_range
  } else {
    let mut p = pos;
    let mut res = PK.no_range;
    let mut stop = false;
    while (let vp = !p; SZ.lt vp limit)
    invariant exists* (vp:SZ.t) (vres:PK.der_range) (vstop:bool).
      pts_to p vp ** pts_to res vres ** pts_to stop vstop ** pts_to c 'b **
      pure (SZ.v vp <= SZ.v limit /\ (vstop ==> vp == limit) /\
            (vres.ok ==> SZ.v vres.lo <= SZ.v vres.hi /\ SZ.v vres.hi <= SZ.v len) /\
            (vstop ==> opt_range_matches vres (X.find_extension (cb 'b len) (SZ.v pos) (SZ.v limit) k)) /\
            (not vstop ==> vres.ok == false /\
               X.find_extension (cb 'b len) (SZ.v pos) (SZ.v limit) k ==
               X.find_extension (cb 'b len) (SZ.v vp) (SZ.v limit) k))
    decreases (SZ.v limit - SZ.v (!p))
    {
      let vp = !p;
      let x = ext_at c len vp limit;
      if (x.x_ok) {
        let hit = ext_oid_is c len x k;
        if (hit) {
          find_extension_hit (cb 'b len) (SZ.v vp) (SZ.v limit) k x;
          res := ({ PK.ok = true; PK.lo = x.x_val_s; PK.hi = x.x_val_e });
          stop := true;
          p := limit;
        } else {
          find_extension_miss (cb 'b len) (SZ.v vp) (SZ.v limit) k x;
          p := x.x_end;
        }
      } else {
        stop := true;
        p := limit;
      }
    };
    !res
  }
}

fn oid_in
  (c:array U8.t) (len:SZ.t) (os oe:SZ.t) (pos limit:SZ.t)
  requires pts_to c 'b ** pure (ok_len 'b len /\ SZ.v oe <= SZ.v len)
  returns r:bool
  ensures pts_to c 'b ** pure (r == X.oid_in (cb 'b len) (SZ.v os) (SZ.v oe) (SZ.v pos) (SZ.v limit))
{
  if (SZ.gte pos limit) {
    false
  } else {
    let mut p = pos;
    let mut res = false;
    let mut stop = false;
    while (let vp = !p; SZ.lt vp limit)
    invariant exists* (vp:SZ.t) (vres:bool) (vstop:bool).
      pts_to p vp ** pts_to res vres ** pts_to stop vstop ** pts_to c 'b **
      pure (SZ.v vp <= SZ.v limit /\ (vstop ==> vp == limit) /\
            (vstop ==> vres == X.oid_in (cb 'b len) (SZ.v os) (SZ.v oe) (SZ.v pos) (SZ.v limit)) /\
            (not vstop ==> vres == false /\
               X.oid_in (cb 'b len) (SZ.v os) (SZ.v oe) (SZ.v pos) (SZ.v limit) ==
               X.oid_in (cb 'b len) (SZ.v os) (SZ.v oe) (SZ.v vp) (SZ.v limit)))
    decreases (SZ.v limit - SZ.v (!p))
    {
      let vp = !p;
      let x = ext_at c len vp limit;
      if (x.x_ok) {
        let eq = range_eq_self c len os oe x.x_oid_s x.x_oid_e;
        if (eq) {
          res := true;
          stop := true;
          p := limit;
        } else {
          p := x.x_end;
        }
      } else {
        stop := true;
        p := limit;
      }
    };
    !res
  }
}
#pop-options

fn understood
  (c:array U8.t) (len:SZ.t) (x:ext_v)
  requires pts_to c 'b **
           pure (ok_len 'b len /\ SZ.v x.x_oid_s <= SZ.v x.x_oid_e /\ SZ.v x.x_oid_e <= SZ.v len)
  returns r:bool
  ensures pts_to c 'b ** pure (r == X.understood (cb 'b len) (to_ext x))
{
  let a = ext_oid_is c len x X.oid_basic_constraints;
  let b = ext_oid_is c len x X.oid_key_usage;
  let d = ext_oid_is c len x X.oid_subject_alt_name;
  let e = ext_oid_is c len x X.oid_ext_key_usage;
  (a || b || d || e)
}

#push-options "--z3rlimit 60"
fn extensions_ok
  (c:array U8.t) (len:SZ.t) (pos limit:SZ.t)
  requires pts_to c 'b ** pure (ok_len 'b len)
  returns r:bool
  ensures pts_to c 'b ** pure (r == X.extensions_ok (cb 'b len) (SZ.v pos) (SZ.v limit))
{
  if (SZ.gte pos limit) {
    true
  } else {
    let mut p = pos;
    let mut ok = true;
    while (let vp = !p; SZ.lt vp limit)
    invariant exists* (vp:SZ.t) (vok:bool).
      pts_to p vp ** pts_to ok vok ** pts_to c 'b **
      pure (SZ.v vp <= SZ.v limit /\
            X.extensions_ok (cb 'b len) (SZ.v pos) (SZ.v limit) ==
            (vok && X.extensions_ok (cb 'b len) (SZ.v vp) (SZ.v limit)))
    decreases (SZ.v limit - SZ.v (!p))
    {
      let vp = !p;
      let x = ext_at c len vp limit;
      if (x.x_ok) {
        let dup = oid_in c len x.x_oid_s x.x_oid_e x.x_end limit;
        let u = understood c len x;
        let nc = ext_oid_is c len x X.oid_name_constraints;
        if (not dup && (not x.x_crit || u) && not nc) {
          p := x.x_end;
        } else {
          ok := false;
          p := limit;
        }
      } else {
        ok := false;
        p := limit;
      }
    };
    !ok
  }
}
#pop-options

#push-options "--z3rlimit 60"
fn ca_allows
  (c:array U8.t) (len:SZ.t) (vs ve below:SZ.t)
  requires pts_to c 'b ** pure (ok_len 'b len)
  returns r:bool
  ensures pts_to c 'b ** pure (r == X.ca_allows (cb 'b len) (SZ.v vs) (SZ.v ve) (SZ.v below))
{
  let s = PK.der_tlv_impl c len 0x30uy vs ve;
  if (s.ok && s.hi = ve) {
    let bo = PK.der_tlv_impl c len 0x01uy s.lo s.hi;
    if (bo.ok) {
      let ff = byte_is c len bo.lo 0xFFuy;
      if (bo.hi = bo.lo +^ 1sz && ff) {
        if (bo.hi = s.hi) {
          true
        } else {
          let i = PK.der_tlv_impl c len 0x02uy bo.hi s.hi;
          if (i.ok && i.hi = s.hi && i.hi = i.lo +^ 1sz) {
            let n = c.(i.lo);
            if (U8.lt n 0x80uy) {
              SZ.lte below (PK.u8_to_sz n)
            } else {
              false
            }
          } else {
            false
          }
        }
      } else {
        false
      }
    } else {
      false
    }
  } else {
    false
  }
}

fn key_usage_allows
  (c:array U8.t) (len:SZ.t) (xs xe:SZ.t) (mask:U8.t)
  requires pts_to c 'b ** pure (ok_len 'b len)
  returns r:bool
  ensures pts_to c 'b ** pure (r == X.key_usage_allows (cb 'b len) (SZ.v xs) (SZ.v xe) mask)
{
  let f = find_extension c len xs xe X.oid_key_usage;
  if (f.ok) {
    let s = PK.der_tlv_impl c len 0x03uy f.lo f.hi;
    if (s.ok && s.hi = f.hi && SZ.lt s.lo s.hi) {
      let u = c.(s.lo);
      if (U8.gt u 7uy) {
        false
      } else if (s.lo +^ 1sz = s.hi) {
        X.has_bit 0uy mask
      } else {
        let v = c.(s.lo +^ 1sz);
        X.has_bit v mask
      }
    } else {
      false
    }
  } else {
    true
  }
}
#pop-options

fn is_server_auth
  (c:array U8.t) (len:SZ.t) (s e:SZ.t)
  requires pts_to c 'b ** pure (ok_len 'b len /\ SZ.v s <= SZ.v e /\ SZ.v e <= SZ.v len)
  returns r:bool
  ensures pts_to c 'b ** pure (r == X.is_server_auth (cb 'b len) (SZ.v s) (SZ.v e))
{
  if (e -^ s = 8sz) {
    let b0 = byte_is c len s 0x2Buy;
    let b1 = byte_is c len (s +^ 1sz) 0x06uy;
    let b2 = byte_is c len (s +^ 2sz) 0x01uy;
    let b3 = byte_is c len (s +^ 3sz) 0x05uy;
    let b4 = byte_is c len (s +^ 4sz) 0x05uy;
    let b5 = byte_is c len (s +^ 5sz) 0x07uy;
    let b6 = byte_is c len (s +^ 6sz) 0x03uy;
    let b7 = byte_is c len (s +^ 7sz) 0x01uy;
    (b0 && b1 && b2 && b3 && b4 && b5 && b6 && b7)
  } else {
    false
  }
}

fn is_any_eku
  (c:array U8.t) (len:SZ.t) (s e:SZ.t)
  requires pts_to c 'b ** pure (ok_len 'b len /\ SZ.v s <= SZ.v e /\ SZ.v e <= SZ.v len)
  returns r:bool
  ensures pts_to c 'b ** pure (r == X.is_any_eku (cb 'b len) (SZ.v s) (SZ.v e))
{
  if (e -^ s = 4sz) {
    let b0 = byte_is c len s 0x55uy;
    let b1 = byte_is c len (s +^ 1sz) 0x1Duy;
    let b2 = byte_is c len (s +^ 2sz) 0x25uy;
    let b3 = byte_is c len (s +^ 3sz) 0x00uy;
    (b0 && b1 && b2 && b3)
  } else {
    false
  }
}

(** [X.eku_server_auth c pos limit false = Some true]. *)
fn eku_server_auth
  (c:array U8.t) (len:SZ.t) (pos limit:SZ.t)
  requires pts_to c 'b ** pure (ok_len 'b len)
  returns r:bool
  ensures pts_to c 'b **
          pure (r == (X.eku_server_auth (cb 'b len) (SZ.v pos) (SZ.v limit) false = Some true))
{
  if (SZ.gt pos limit) {
    false
  } else {
    let mut p = pos;
    let mut found = false;
    let mut fail = false;
    while (let vp = !p; SZ.lt vp limit)
    invariant exists* (vp:SZ.t) (vfound:bool) (vfail:bool).
      pts_to p vp ** pts_to found vfound ** pts_to fail vfail ** pts_to c 'b **
      pure (SZ.v vp <= SZ.v limit /\ (vfail ==> vp == limit) /\
            X.eku_server_auth (cb 'b len) (SZ.v pos) (SZ.v limit) false ==
            (if vfail then None else X.eku_server_auth (cb 'b len) (SZ.v vp) (SZ.v limit) vfound))
    decreases (SZ.v limit - SZ.v (!p))
    {
      let vp = !p;
      let o = PK.der_tlv_impl c len 0x06uy vp limit;
      if (o.ok) {
        let sa = is_server_auth c len o.lo o.hi;
        let an = is_any_eku c len o.lo o.hi;
        let vf = !found;
        found := (vf || sa || an);
        p := o.hi;
      } else {
        fail := true;
        p := limit;
      }
    };
    let vfail = !fail;
    let vfound = !found;
    (not vfail && vfound)
  }
}

fn ext_key_usage_ok
  (c:array U8.t) (len:SZ.t) (xs xe:SZ.t)
  requires pts_to c 'b ** pure (ok_len 'b len)
  returns r:bool
  ensures pts_to c 'b ** pure (r == X.ext_key_usage_ok (cb 'b len) (SZ.v xs) (SZ.v xe))
{
  let f = find_extension c len xs xe X.oid_ext_key_usage;
  if (f.ok) {
    let s = PK.der_tlv_impl c len 0x30uy f.lo f.hi;
    if (s.ok && s.hi = f.hi) {
      eku_server_auth c len s.lo s.hi
    } else {
      false
    }
  } else {
    true
  }
}
