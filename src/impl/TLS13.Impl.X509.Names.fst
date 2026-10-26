module TLS13.Impl.X509.Names

(** Verified server-name matching against a certificate's subjectAltName,
    as a transcription of [TLS13.X509.Spec.subject_alt_name_ok]. *)

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
open TLS13.Impl.X509.Fields

module A = Pulse.Lib.Array
module B = TLS13.Bytes
module Cast = FStar.Int.Cast
module PK = TLS13.Impl.X509.PublicKey
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U16 = FStar.UInt16
module U8 = FStar.UInt8
module X = TLS13.X509.Spec

inline_for_extraction noextract unfold let ( +^ ) = SZ.add
inline_for_extraction noextract unfold let ( -^ ) = SZ.sub

inline_for_extraction
let lower (x:U8.t) : r:U8.t{r == X.lower x} =
  if U8.gte x 0x41uy && U8.lte x 0x5Auy then U8.add x 0x20uy else x

(** [X.ci_eq] across two buffers, within range. *)
fn ci_eq
  (a:array U8.t) (alen:SZ.t) (ai:SZ.t)
  (b:array U8.t) (blen:SZ.t) (bi:SZ.t) (n:SZ.t)
  requires pts_to a 'x ** pts_to b 'y **
           pure (ok_len 'x alen /\ ok_len 'y blen /\
                 SZ.v ai + SZ.v n <= SZ.v alen /\ SZ.v bi + SZ.v n <= SZ.v blen)
  returns r:bool
  ensures pts_to a 'x ** pts_to b 'y **
          pure (r == X.ci_eq (cb 'x alen) (SZ.v ai) (cb 'y blen) (SZ.v bi) (SZ.v n))
{
  let mut i = 0sz;
  let mut ok = true;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi:SZ.t) (vok:bool).
    pts_to i vi ** pts_to ok vok ** pts_to a 'x ** pts_to b 'y **
    pure (SZ.v vi <= SZ.v n /\
          X.ci_eq (cb 'x alen) (SZ.v ai) (cb 'y blen) (SZ.v bi) (SZ.v n) ==
          (vok && X.ci_eq (cb 'x alen) (SZ.v ai + SZ.v vi) (cb 'y blen)
                    (SZ.v bi + SZ.v vi) (SZ.v n - SZ.v vi)))
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    let x = a.(ai +^ vi);
    let y = b.(bi +^ vi);
    if (lower x = lower y) {
      i := vi +^ 1sz;
    } else {
      ok := false;
      i := n;
    }
  };
  !ok
}

fn dot_free
  (a:array U8.t) (alen:SZ.t) (s n:SZ.t)
  requires pts_to a 'x ** pure (ok_len 'x alen /\ SZ.v s + SZ.v n <= SZ.v alen)
  returns r:bool
  ensures pts_to a 'x ** pure (r == X.dot_free (cb 'x alen) (SZ.v s) (SZ.v n))
{
  let mut i = 0sz;
  let mut ok = true;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi:SZ.t) (vok:bool).
    pts_to i vi ** pts_to ok vok ** pts_to a 'x **
    pure (SZ.v vi <= SZ.v n /\
          X.dot_free (cb 'x alen) (SZ.v s) (SZ.v n) ==
          (vok && X.dot_free (cb 'x alen) (SZ.v s + SZ.v vi) (SZ.v n - SZ.v vi)))
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    let x = a.(s +^ vi);
    if (x <> 0x2Euy) {
      i := vi +^ 1sz;
    } else {
      ok := false;
      i := n;
    }
  };
  !ok
}

#push-options "--z3rlimit 60"
fn dns_matches
  (c:array U8.t) (len:SZ.t) (ps pe:SZ.t)
  (h:array U8.t) (hlen:SZ.t)
  requires pts_to c 'b ** pts_to h 'hb **
           pure (ok_len 'b len /\ ok_len 'hb hlen /\ SZ.v pe <= SZ.v len)
  returns r:bool
  ensures pts_to c 'b ** pts_to h 'hb **
          pure (r == X.dns_matches (cb 'b len) (SZ.v ps) (SZ.v pe) (cb 'hb hlen))
{
  if (SZ.gt ps pe) {
    false
  } else {
    let lp = pe -^ ps;
    let exact =
      if (SZ.gt lp 0sz && lp = hlen) {
        ci_eq c len ps h hlen 0sz lp
      } else {
        false
      };
    if (exact) {
      true
    } else if (SZ.gte lp 4sz) {
      let star = byte_is c len ps 0x2Auy;
      let dot = byte_is c len (ps +^ 1sz) 0x2Euy;
      if (star && dot) {
        let nd = dot_free c len (ps +^ 2sz) (lp -^ 2sz);
        if (not nd && SZ.gte hlen lp) {
          let first = hlen -^ (lp -^ 1sz);
          let df = dot_free h hlen 0sz first;
          if (df) {
            ci_eq c len (ps +^ 1sz) h hlen first (lp -^ 1sz)
          } else {
            false
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
}
#pop-options

(** The digit at [h[i]], or 10. *)
let digit_val (h:B.bytes) (i:nat) : U8.t =
  if i < B.length h && X.is_digit (Seq.index h i) then U8.uint_to_t (X.digit (Seq.index h i))
  else 10uy

fn digit_at
  (h:array U8.t) (hlen:SZ.t) (i:SZ.t)
  requires pts_to h 'hb ** pure (ok_len 'hb hlen)
  returns r:U8.t
  ensures pts_to h 'hb **
          pure (r == digit_val (cb 'hb hlen) (SZ.v i))
{
  if (SZ.lt i hlen) {
    let x = h.(i);
    if (U8.gte x 0x30uy && U8.lte x 0x39uy) {
      U8.sub x 0x30uy
    } else {
      10uy
    }
  } else {
    10uy
  }
}

type octet = {
  o_ok: bool;
  o_val: U8.t;
  o_end: SZ.t;
}

let octet_matches (r:octet) (o:option (U8.t & nat)) : prop =
  match o with
  | Some (v, e) -> r.o_ok == true /\ r.o_val == v /\ SZ.v r.o_end == e
  | None -> r.o_ok == false

inline_for_extraction noextract
let no_octet : octet = { o_ok = false; o_val = 0uy; o_end = 0sz }

let u16_to_u8 (x:U16.t{U16.v x <= 255}) : r:U8.t{r == U8.uint_to_t (U16.v x)} =
  let r = Cast.uint16_to_uint8 x in
  assert (U8.v r == U16.v x % 256);
  FStar.Math.Lemmas.small_mod (U16.v x) 256;
  U8.v_inj r (U8.uint_to_t (U16.v x));
  r

#push-options "--z3rlimit 80"
fn dec_octet
  (h:array U8.t) (hlen:SZ.t) (pos:SZ.t)
  requires pts_to h 'hb ** pure (ok_len 'hb hlen /\ SZ.v pos <= SZ.v hlen)
  returns r:octet
  ensures pts_to h 'hb **
          pure (octet_matches r (X.dec_octet (cb 'hb hlen) (SZ.v pos)) /\
                (r.o_ok ==> SZ.v r.o_end <= SZ.v hlen))
{
  let d0 = digit_at h hlen pos;
  if (d0 = 10uy) {
    no_octet
  } else {
    let d1 = digit_at h hlen (pos +^ 1sz);
    if (d1 = 10uy) {
      ({ o_ok = true; o_val = d0; o_end = pos +^ 1sz })
    } else if (d0 = 0uy) {
      no_octet
    } else {
      let d2 = digit_at h hlen (pos +^ 2sz);
      if (d2 = 10uy) {
        ({ o_ok = true; o_val = U8.add (U8.mul 10uy d0) d1; o_end = pos +^ 2sz })
      } else {
        let d3 = digit_at h hlen (pos +^ 3sz);
        if (d3 <> 10uy) {
          no_octet
        } else {
          let v = U16.add (U16.add (U16.mul 100us (Cast.uint8_to_uint16 d0))
                                   (U16.mul 10us (Cast.uint8_to_uint16 d1)))
                          (Cast.uint8_to_uint16 d2);
          if (U16.gt v 255us) {
            no_octet
          } else {
            ({ o_ok = true; o_val = u16_to_u8 v; o_end = pos +^ 3sz })
          }
        }
      }
    }
  }
}
#pop-options

fn dot_octet
  (h:array U8.t) (hlen:SZ.t) (pos:SZ.t)
  requires pts_to h 'hb ** pure (ok_len 'hb hlen /\ SZ.v pos <= SZ.v hlen)
  returns r:octet
  ensures pts_to h 'hb **
          pure (octet_matches r (X.dot_octet (cb 'hb hlen) (SZ.v pos)) /\
                (r.o_ok ==> SZ.v r.o_end <= SZ.v hlen))
{
  if (SZ.lt pos hlen) {
    let x = h.(pos);
    if (x = 0x2Euy) {
      dec_octet h hlen (pos +^ 1sz)
    } else {
      no_octet
    }
  } else {
    no_octet
  }
}

type ip_v = {
  ip_ok: bool;
  a0: U8.t;
  a1: U8.t;
  a2: U8.t;
  a3: U8.t;
}

let to_ipv4 (r:ip_v) : X.ipv4 = { X.ip0 = r.a0; X.ip1 = r.a1; X.ip2 = r.a2; X.ip3 = r.a3 }

let to_ip (r:ip_v) : option X.ipv4 = if r.ip_ok then Some (to_ipv4 r) else None

inline_for_extraction noextract
let no_ip : ip_v = { ip_ok = false; a0 = 0uy; a1 = 0uy; a2 = 0uy; a3 = 0uy }

#push-options "--z3rlimit 60"
fn ipv4_address
  (h:array U8.t) (hlen:SZ.t)
  requires pts_to h 'hb ** pure (ok_len 'hb hlen)
  returns r:ip_v
  ensures pts_to h 'hb ** pure (to_ip r == X.ipv4_address (cb 'hb hlen))
{
  let o0 = dec_octet h hlen 0sz;
  if (o0.o_ok) {
    let o1 = dot_octet h hlen o0.o_end;
    if (o1.o_ok) {
      let o2 = dot_octet h hlen o1.o_end;
      if (o2.o_ok) {
        let o3 = dot_octet h hlen o2.o_end;
        if (o3.o_ok && o3.o_end = hlen) {
          ({ ip_ok = true; a0 = o0.o_val; a1 = o1.o_val; a2 = o2.o_val; a3 = o3.o_val })
        } else {
          no_ip
        }
      } else {
        no_ip
      }
    } else {
      no_ip
    }
  } else {
    no_ip
  }
}
#pop-options

fn ip_is
  (c:array U8.t) (len:SZ.t) (s e:SZ.t) (ip:ip_v)
  requires pts_to c 'b ** pure (ok_len 'b len /\ SZ.v s <= SZ.v e /\ SZ.v e <= SZ.v len)
  returns r:bool
  ensures pts_to c 'b ** pure (r == X.ip_is (cb 'b len) (SZ.v s) (SZ.v e) (to_ipv4 ip))
{
  if (e -^ s = 4sz) {
    let b0 = byte_is c len s ip.a0;
    let b1 = byte_is c len (s +^ 1sz) ip.a1;
    let b2 = byte_is c len (s +^ 2sz) ip.a2;
    let b3 = byte_is c len (s +^ 3sz) ip.a3;
    (b0 && b1 && b2 && b3)
  } else {
    false
  }
}

(** [X.general_names_match c pos limit h ip false = Some true]. *)
#push-options "--z3rlimit 80"
fn general_names_match
  (c:array U8.t) (len:SZ.t) (pos limit:SZ.t)
  (h:array U8.t) (hlen:SZ.t) (ip:ip_v)
  requires pts_to c 'b ** pts_to h 'hb ** pure (ok_len 'b len /\ ok_len 'hb hlen)
  returns r:bool
  ensures pts_to c 'b ** pts_to h 'hb **
          pure (r == (X.general_names_match (cb 'b len) (SZ.v pos) (SZ.v limit)
                        (cb 'hb hlen) (to_ip ip) false = Some true))
{
  if (SZ.gt pos limit) {
    false
  } else {
    let mut p = pos;
    let mut found = false;
    let mut fail = false;
    while (let vp = !p; SZ.lt vp limit)
    invariant exists* (vp:SZ.t) (vfound:bool) (vfail:bool).
      pts_to p vp ** pts_to found vfound ** pts_to fail vfail ** pts_to c 'b ** pts_to h 'hb **
      pure (SZ.v vp <= SZ.v limit /\ (vfail ==> vp == limit) /\
            X.general_names_match (cb 'b len) (SZ.v pos) (SZ.v limit) (cb 'hb hlen) (to_ip ip) false ==
            (if vfail then None
             else X.general_names_match (cb 'b len) (SZ.v vp) (SZ.v limit) (cb 'hb hlen)
                    (to_ip ip) vfound))
    decreases (SZ.v limit - SZ.v (!p))
    {
      let vp = !p;
      let g = der_any c len vp limit;
      if (g.ok) {
        let tag = c.(vp);
        let this =
          if (ip.ip_ok) {
            if (tag = 0x87uy) { ip_is c len g.lo g.hi ip } else { false }
          } else {
            if (tag = 0x82uy) { dns_matches c len g.lo g.hi h hlen } else { false }
          };
        let vf = !found;
        found := (vf || this);
        p := g.hi;
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
#pop-options

fn subject_alt_name_ok
  (c:array U8.t) (len:SZ.t) (xs xe:SZ.t)
  (h:array U8.t) (hlen:SZ.t)
  requires pts_to c 'b ** pts_to h 'hb ** pure (ok_len 'b len /\ ok_len 'hb hlen)
  returns r:bool
  ensures pts_to c 'b ** pts_to h 'hb **
          pure (r == X.subject_alt_name_ok (cb 'b len) (SZ.v xs) (SZ.v xe) (cb 'hb hlen))
{
  let f = find_extension c len xs xe X.oid_subject_alt_name;
  if (f.ok) {
    let s = PK.der_tlv_impl c len 0x30uy f.lo f.hi;
    if (s.ok && s.hi = f.hi && SZ.gt hlen 0sz) {
      let ip = ipv4_address h hlen;
      general_names_match c len s.lo s.hi h hlen ip
    } else {
      false
    }
  } else {
    false
  }
}
