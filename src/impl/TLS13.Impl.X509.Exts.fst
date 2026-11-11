module TLS13.Impl.X509.Exts

(** The extension checks of [TLS13.X509.Chain], over the [Extensions] list
    of a parsed certificate exposed by [TLS13.Impl.X509.Iter]: the elements
    left at offset [off] of [w] are [nl_at X.k_Extension w off n l]. *)

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Trade
open ASN1.Base
open ASN1.Pulse.Rel
open TLS13.Wire.Generated.X509.Impl
open TLS13.Impl.X509.ASN1
open TLS13.Impl.X509.Iter
open TLS13.Impl.X509.Rels

module A = Pulse.Lib.Array
module B = TLS13.Bytes
module C = TLS13.X509.Chain
module E = ASN1.Spec.Content.Enc
module KS = TLS13.X509.KeySpec
module L = FStar.List.Tot
module S = Pulse.Lib.Slice
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module X = TLS13.Wire.Generated.X509
module XP = TLS13.X509.Profile

let octets_id (y: asn1_octetstring_t)
: Lemma (E.leaf_enc ASN1_OCTETSTRING y == y)
= assert_norm (E.leaf_enc ASN1_OCTETSTRING y == y)

(** {2 Extension OIDs} *)

inline_for_extraction noextract
let eq_ext (k: U8.t) : eq_from_t [0x55uy; 0x1Duy; k] =
  norm [delta_only [`%mk_eq]; zeta; iota; primops] (mk_eq [0x55uy; 0x1Duy; k])

fn oid_ext (k: U8.t) (s: S.slice U8.t) (#pm: perm) (#w: Ghost.erased (Seq.seq U8.t))
  requires S.pts_to s #pm w
  returns r: bool
  ensures S.pts_to s #pm w ** pure (r <==> KS.bytes_is w [0x55uy; 0x1Duy; k])
{
  S.pts_to_len s;
  let r = eq_ext k s 0sz #pm #w;
  assert (pure (Seq.slice w 0 (Seq.length w) `Seq.equal` w));
  r
}

(** Whether the extension [x] is [2.5.29.k]. *)
fn ext_is (k: U8.t) (x: t_Extension) (#pm: perm) (#h: Ghost.erased XP.extension)
  requires arel true d_Extension pm x h
  returns r: bool
  ensures arel true d_Extension pm x h ** pure (r == C.ext_is h k)
{
  ext_eq pm x h;
  rewrite (arel true d_Extension pm x h) as (ext_rel pm x h);
  unfold ext_rel;
  unfold (oid_rel pm x.extnID (fst (reveal h)));
  unfold (prel_slice_ser (E.leaf_enc ASN1_OID) pm x.extnID (fst (reveal h)));
  let r = oid_ext k x.extnID;
  fold (prel_slice_ser (E.leaf_enc ASN1_OID) pm x.extnID (fst (reveal h)));
  fold (oid_rel pm x.extnID (fst (reveal h)));
  fold (ext_rel pm x h);
  rewrite (ext_rel pm x h) as (arel true d_Extension pm x h);
  r
}

(** {2 Finding an extension} *)

type found = {
  fd_ok: bool;
  fd_some: bool;
  fd_len: SZ.t;
}

(** [r] says what [o] is, with the value in [d[0, fd_len)]. *)
let found_ok (r: found) (o: option B.bytes) (d: Seq.seq U8.t) : prop =
  r.fd_ok ==>
  (if r.fd_some then SZ.v r.fd_len <= Seq.length d /\ o == Some (Seq.slice d 0 (SZ.v r.fd_len))
   else o == None)

(** Copy the value of extension [x] into [buf]. *)
fn ext_value (x: t_Extension) (#pm: perm) (#h: Ghost.erased XP.extension)
  (buf: A.array U8.t) (blen: SZ.t) (#old: Ghost.erased (Seq.seq U8.t))
  requires arel true d_Extension pm x h ** A.pts_to buf old ** pure (A.length buf == SZ.v blen)
  returns r: found
  ensures arel true d_Extension pm x h ** (exists* d. A.pts_to buf d **
          pure (Seq.length d == Seq.length old /\ r.fd_some /\ found_ok r (Some (XP.ext_value h)) d))
{
  ext_eq pm x h;
  rewrite (arel true d_Extension pm x h) as (ext_rel pm x h);
  unfold ext_rel;
  unfold (prel_slice_ser (E.leaf_enc ASN1_OCTETSTRING) pm x.extnValue (snd (snd (reveal h))));
  with wv. assert (S.pts_to x.extnValue #pm wv);
  octets_id (snd (snd (reveal h)));
  S.pts_to_len x.extnValue;
  let n = copy_slice x.extnValue buf blen;
  let empty = (S.len x.extnValue = 0sz);
  fold (prel_slice_ser (E.leaf_enc ASN1_OCTETSTRING) pm x.extnValue (snd (snd (reveal h))));
  fold (ext_rel pm x h);
  rewrite (ext_rel pm x h) as (arel true d_Extension pm x h);
  ({ fd_ok = (SZ.gt n 0sz || empty); fd_some = true; fd_len = n })
}

#push-options "--z3rlimit 80 --fuel 2 --ifuel 2"
(** [C.find_extension l k], copied into [buf]. *)
fn find_ext (input: S.slice U8.t) (count: SZ.t) (#q: perm) (#w: Ghost.erased (Seq.seq U8.t))
  (#l: Ghost.erased (list XP.extension)) (k: U8.t)
  (buf: A.array U8.t) (blen: SZ.t) (#old: Ghost.erased (Seq.seq U8.t))
  requires S.pts_to input #q w ** A.pts_to buf old **
           pure (nl_at X.k_Extension w 0 (SZ.v count) l /\ A.length buf == SZ.v blen)
  returns r: found
  ensures S.pts_to input #q w ** (exists* d. A.pts_to buf d **
          pure (Seq.length d == Seq.length old /\ found_ok r (C.find_extension l k) d))
{
  let mut off = 0sz;
  let mut i = count;
  let mut res = { fd_ok = true; fd_some = false; fd_len = 0sz };
  let mut fin = false;
  nl_rest_eq X.k_Extension w 0 (SZ.v count) l;
  while (let vi = !i; let vf = !fin; (not vf && SZ.gt vi 0sz))
  invariant exists* (voff vi: SZ.t) (vr: found) (vf: bool) (d: Seq.seq U8.t).
    pts_to off voff ** pts_to i vi ** pts_to res vr ** pts_to fin vf **
    S.pts_to input #q w ** A.pts_to buf d **
    pure (Seq.length d == Seq.length old /\
          (vf ==> found_ok vr (C.find_extension l k) d) /\
          (not vf ==> nl_at X.k_Extension w (SZ.v voff) (SZ.v vi) (nl_rest X.k_Extension w (SZ.v voff) (SZ.v vi)) /\
                      C.find_extension l k == C.find_extension (nl_rest X.k_Extension w (SZ.v voff) (SZ.v vi)) k /\
                      vr == { fd_ok = true; fd_some = false; fd_len = 0sz }))
  decreases ((if !fin then 0 else 1) + SZ.v (!i))
  {
    let vi = !i;
    let voff = !off;
    let p = nl_elem validate_Extension parse_Extension input voff (SZ.v vi - 1) #q #w
      #(nl_rest X.k_Extension w (SZ.v voff) (SZ.v vi));
    let x = fst p;
    with h. assert (arel true d_Extension q (fst p) h);
    rewrite each (fst p) as x;
    let hit = ext_is k x;
    if hit {
      let r = ext_value x buf blen;
      res := r;
      fin := true;
      elim_trade (arel true d_Extension q x h) (S.pts_to input #q w);
    } else {
      elim_trade (arel true d_Extension q x h) (S.pts_to input #q w);
      nl_rest_eq X.k_Extension w (SZ.v (snd p)) (SZ.v vi - 1) (L.tl (nl_rest X.k_Extension w (SZ.v voff) (SZ.v vi)));
      off := snd p;
      i := SZ.sub vi 1sz;
    }
  };
  let vf = !fin;
  if vf {
    !res
  } else {
    with voff vi. assert (pts_to off voff ** pts_to i vi);
    nl_at_nil X.k_Extension w (SZ.v voff) (nl_rest X.k_Extension w (SZ.v voff) (SZ.v vi));
    !res
  }
}
#pop-options

(** {2 Extension list well-formedness} *)

let crit_val (c: t_Extension_critical_opt) : bool =
  match c with
  | Extension_critical_absent -> false
  | Extension_critical_present a -> a

ghost fn crit_info (pm: perm) (c: t_Extension_critical_opt) (y: XP.extension)
  requires crit_m pm c y
  ensures crit_m pm c y ** pure (crit_val c == XP.ext_critical y)
{
  if (Extension_critical_absent? c) {
    if (Default? (fst (snd y))) {
      ()
    } else {
      rewrite (crit_m pm c y) as pure False;
      unreachable ()
    }
  } else {
    if (Nondefault? (fst (snd y))) {
      rewrite (crit_m pm c y) as pure (Extension_critical_present?.v c == Nondefault?.v' (fst (snd y)));
      rewrite (pure (Extension_critical_present?.v c == Nondefault?.v' (fst (snd y)))) as (crit_m pm c y)
    } else {
      rewrite (crit_m pm c y) as pure False;
      unreachable ()
    }
  }
}

(** Whether the extension [x] is marked critical. *)
fn ext_crit (x: t_Extension) (#pm: perm) (#h: Ghost.erased XP.extension)
  requires arel true d_Extension pm x h
  returns r: bool
  ensures arel true d_Extension pm x h ** pure (r == XP.ext_critical h)
{
  ext_eq pm x h;
  rewrite (arel true d_Extension pm x h) as (ext_rel pm x h);
  unfold ext_rel;
  crit_info pm x.critical h;
  let r = crit_val x.critical;
  fold (ext_rel pm x h);
  rewrite (ext_rel pm x h) as (arel true d_Extension pm x h);
  r
}

(** Whether the extensions [x] and [y] have the same OID. *)
fn ext_same (x: t_Extension) (#px: perm) (#hx: Ghost.erased XP.extension)
  (y: t_Extension) (#py: perm) (#hy: Ghost.erased XP.extension)
  requires arel true d_Extension px x hx ** arel true d_Extension py y hy
  returns r: bool
  ensures arel true d_Extension px x hx ** arel true d_Extension py y hy **
          pure (r == Seq.eq (C.ext_oid_bytes hx) (C.ext_oid_bytes hy))
{
  ext_eq px x hx;
  ext_eq py y hy;
  rewrite (arel true d_Extension px x hx) as (ext_rel px x hx);
  rewrite (arel true d_Extension py y hy) as (ext_rel py y hy);
  unfold (ext_rel px x hx);
  unfold (ext_rel py y hy);
  unfold (oid_rel px x.extnID (fst (reveal hx)));
  unfold (oid_rel py y.extnID (fst (reveal hy)));
  unfold (prel_slice_ser (E.leaf_enc ASN1_OID) px x.extnID (fst (reveal hx)));
  unfold (prel_slice_ser (E.leaf_enc ASN1_OID) py y.extnID (fst (reveal hy)));
  let r = slice_eq x.extnID y.extnID;
  Seq.lemma_eq_intro (C.ext_oid_bytes hx) (C.ext_oid_bytes hx);
  assert (pure (r == Seq.eq (C.ext_oid_bytes hx) (C.ext_oid_bytes hy)));
  fold (prel_slice_ser (E.leaf_enc ASN1_OID) px x.extnID (fst (reveal hx)));
  fold (prel_slice_ser (E.leaf_enc ASN1_OID) py y.extnID (fst (reveal hy)));
  fold (oid_rel px x.extnID (fst (reveal hx)));
  fold (oid_rel py y.extnID (fst (reveal hy)));
  fold (ext_rel px x hx);
  fold (ext_rel py y hy);
  rewrite (ext_rel px x hx) as (arel true d_Extension px x hx);
  rewrite (ext_rel py y hy) as (arel true d_Extension py y hy);
  r
}

#push-options "--z3rlimit 80 --fuel 2 --ifuel 2"
(** [C.oid_in] of [x]'s OID over the [count] elements at [off]. *)
fn oid_in_rest (x: t_Extension) (#px: perm) (#hx: Ghost.erased XP.extension)
  (input: S.slice U8.t) (off0: SZ.t) (count: SZ.t) (#q: perm) (#w: Ghost.erased (Seq.seq U8.t))
  requires arel true d_Extension px x hx ** S.pts_to input #q w **
           pure (nl_at X.k_Extension w (SZ.v off0) (SZ.v count) (nl_rest X.k_Extension w (SZ.v off0) (SZ.v count)))
  returns r: bool
  ensures arel true d_Extension px x hx ** S.pts_to input #q w **
          pure (r == C.oid_in (C.ext_oid_bytes hx) (nl_rest X.k_Extension w (SZ.v off0) (SZ.v count)))
{
  let mut off = off0;
  let mut i = count;
  let mut fin = false;
  while (let vi = !i; let vf = !fin; (not vf && SZ.gt vi 0sz))
  invariant exists* (voff vi: SZ.t) (vf: bool).
    pts_to off voff ** pts_to i vi ** pts_to fin vf **
    arel true d_Extension px x hx ** S.pts_to input #q w **
    pure ((vf ==> C.oid_in (C.ext_oid_bytes hx) (nl_rest X.k_Extension w (SZ.v off0) (SZ.v count))) /\
          (not vf ==> nl_at X.k_Extension w (SZ.v voff) (SZ.v vi) (nl_rest X.k_Extension w (SZ.v voff) (SZ.v vi)) /\
                      C.oid_in (C.ext_oid_bytes hx) (nl_rest X.k_Extension w (SZ.v off0) (SZ.v count)) ==
                      C.oid_in (C.ext_oid_bytes hx) (nl_rest X.k_Extension w (SZ.v voff) (SZ.v vi))))
  decreases ((if !fin then 0 else 1) + SZ.v (!i))
  {
    let vi = !i;
    let voff = !off;
    let p = nl_elem validate_Extension parse_Extension input voff (SZ.v vi - 1) #q #w
      #(nl_rest X.k_Extension w (SZ.v voff) (SZ.v vi));
    let y = fst p;
    with h. assert (arel true d_Extension q (fst p) h);
    rewrite each (fst p) as y;
    let same = ext_same x y;
    elim_trade (arel true d_Extension q y h) (S.pts_to input #q w);
    if same {
      fin := true;
    } else {
      nl_rest_eq X.k_Extension w (SZ.v (snd p)) (SZ.v vi - 1) (L.tl (nl_rest X.k_Extension w (SZ.v voff) (SZ.v vi)));
      off := snd p;
      i := SZ.sub vi 1sz;
    }
  };
  let vf = !fin;
  if vf {
    true
  } else {
    with voff vi. assert (pts_to off voff ** pts_to i vi);
    nl_at_nil X.k_Extension w (SZ.v voff) (nl_rest X.k_Extension w (SZ.v voff) (SZ.v vi));
    false
  }
}

(** One element of [C.extensions_ok]: [x] is not repeated in the [n]
    elements at [off], is understood if critical, and is not name
    constraints. *)
fn ext_one_ok (x: t_Extension) (#px: perm) (#hx: Ghost.erased XP.extension)
  (input: S.slice U8.t) (off: SZ.t) (n: SZ.t) (#q: perm) (#w: Ghost.erased (Seq.seq U8.t))
  requires arel true d_Extension px x hx ** S.pts_to input #q w **
           pure (nl_at X.k_Extension w (SZ.v off) (SZ.v n) (nl_rest X.k_Extension w (SZ.v off) (SZ.v n)))
  returns r: bool
  ensures arel true d_Extension px x hx ** S.pts_to input #q w **
          pure (r == (not (C.oid_in (C.ext_oid_bytes hx) (nl_rest X.k_Extension w (SZ.v off) (SZ.v n))) &&
                      (not (XP.ext_critical hx) || C.understood hx) &&
                      not (C.ext_is hx C.oid_name_constraints)))
{
  let dup = oid_in_rest x input off n;
  let crit = ext_crit x;
  let bc = ext_is C.oid_basic_constraints x;
  let ku = ext_is C.oid_key_usage x;
  let san = ext_is C.oid_subject_alt_name x;
  let eku = ext_is C.oid_ext_key_usage x;
  let nc = ext_is C.oid_name_constraints x;
  (not dup && (not crit || bc || ku || san || eku) && not nc)
}

ghost fn halve (s: S.slice U8.t) (#q: perm) (#w: Seq.seq U8.t)
  requires S.pts_to s #q w
  ensures S.pts_to s #(q /. 2.0R) w ** S.pts_to s #(q /. 2.0R) w
{
  S.share s
}

ghost fn unhalve (s: S.slice U8.t) (#q: perm) (#w: Seq.seq U8.t)
  requires S.pts_to s #(q /. 2.0R) w ** S.pts_to s #(q /. 2.0R) w
  ensures S.pts_to s #q w
{
  S.gather s;
  rewrite (S.pts_to s #(q /. 2.0R +. q /. 2.0R) w) as (S.pts_to s #q w)
}

(** [C.extensions_ok l], failing closed. *)
fn exts_ok (input: S.slice U8.t) (count: SZ.t) (#q: perm) (#w: Ghost.erased (Seq.seq U8.t))
  (#l: Ghost.erased (list XP.extension))
  requires S.pts_to input #q w ** pure (nl_at X.k_Extension w 0 (SZ.v count) l)
  returns r: bool
  ensures S.pts_to input #q w ** pure (r ==> C.extensions_ok l)
{
  let mut off = 0sz;
  let mut i = count;
  let mut ok = true;
  nl_rest_eq X.k_Extension w 0 (SZ.v count) l;
  while (let vi = !i; let vo = !ok; (vo && SZ.gt vi 0sz))
  invariant exists* (voff vi: SZ.t) (vo: bool).
    pts_to off voff ** pts_to i vi ** pts_to ok vo ** S.pts_to input #q w **
    pure (vo ==> nl_at X.k_Extension w (SZ.v voff) (SZ.v vi) (nl_rest X.k_Extension w (SZ.v voff) (SZ.v vi)) /\
                 (C.extensions_ok (nl_rest X.k_Extension w (SZ.v voff) (SZ.v vi)) ==> C.extensions_ok l))
  decreases ((if !ok then 1 else 0) + SZ.v (!i))
  {
    let vi = !i;
    let voff = !off;
    halve input;
    let p = nl_elem validate_Extension parse_Extension input voff (SZ.v vi - 1) #(q /. 2.0R) #w
      #(nl_rest X.k_Extension w (SZ.v voff) (SZ.v vi));
    let x = fst p;
    with h. assert (arel true d_Extension (q /. 2.0R) (fst p) h);
    rewrite each (fst p) as x;
    nl_rest_eq X.k_Extension w (SZ.v (snd p)) (SZ.v vi - 1) (L.tl (nl_rest X.k_Extension w (SZ.v voff) (SZ.v vi)));
    let good = ext_one_ok x input (snd p) (SZ.sub vi 1sz);
    elim_trade (arel true d_Extension (q /. 2.0R) x h) (S.pts_to input #(q /. 2.0R) w);
    unhalve input;
    if good {
      off := snd p;
      i := SZ.sub vi 1sz;
    } else {
      ok := false;
    }
  };
  let vo = !ok;
  if vo {
    with voff vi. assert (pts_to off voff ** pts_to i vi);
    nl_at_nil X.k_Extension w (SZ.v voff) (nl_rest X.k_Extension w (SZ.v voff) (SZ.v vi));
    true
  } else {
    false
  }
}
#pop-options
