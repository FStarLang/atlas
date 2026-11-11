module TLS13.Impl.X509.Iter

(** Walking the SEQUENCE OFs that the parsers everparse-asn1 generates
    return, and copying and comparing the byte strings they point to.

    A parsed SEQUENCE OF is the serialized chunk of input holding its
    elements; [ml_open] exposes that chunk and the element count, and
    [nl_elem] parses the element at an offset into it, with the generated
    validator (to find the element's end) and parser. The elements left at
    offset [off] are [nl_at k w off n l]. *)

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Trade
open ASN1.Base
open ASN1.Pulse.Rel

module A = Pulse.Lib.Array
module It = LowParse.PulseParse.Iterator
module ItT = LowParse.PulseParse.Iterator.Type
module IO = LowParse.PulseParse.Iterator.IntOps
module LP = LowParse.Spec.Base
module LPB = LowParse.PulseParse.Base
module LPS = LowParse.Pulse.Base
module PP = ASN1.Pulse.Parse
module PS = ASN1.Pulse.ParseSeqOf
module S = Pulse.Lib.Slice
module SU = Pulse.Lib.Slice.Util
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module VC = LowParse.Spec.VCList
module XP = TLS13.X509.Profile

open ASN1.Spec.Interpreter

(** {2 Lists} *)

let nl_at (#s: _) (k: asn1_k s) (w: Seq.seq U8.t) (off: nat) (n: nat) (l: list (asn1_t k)) : prop =
  off <= Seq.length w /\
  (match LP.parse (VC.parse_nlist n #asn1_strong_parser_kind (asn1_as_parser k)) (Seq.slice w off (Seq.length w)) with
   | Some (l', _) -> l' == l
   | None -> False)

(** The elements at [off], when [nl_at] holds for some list. *)
let nl_rest (#s: _) (k: asn1_k s) (w: Seq.seq U8.t) (off: nat) (n: nat) : GTot (list (asn1_t k)) =
  if off <= Seq.length w then
    (match LP.parse (VC.parse_nlist n #asn1_strong_parser_kind (asn1_as_parser k)) (Seq.slice w off (Seq.length w)) with
     | Some (l', _) -> l'
     | None -> [])
  else []

let nl_rest_eq (#s: _) (k: asn1_k s) (w: Seq.seq U8.t) (off: nat) (n: nat) (l: list (asn1_t k))
: Lemma (requires nl_at k w off n l) (ensures nl_rest k w off n == l /\ nl_at k w off n (nl_rest k w off n))
= ()

let nl_at_nil (#s: _) (k: asn1_k s) (w: Seq.seq U8.t) (off: nat) (l: list (asn1_t k))
: Lemma (requires nl_at k w off 0 l) (ensures l == [])
= VC.parse_nlist_eq 0 #asn1_strong_parser_kind (asn1_as_parser k) (Seq.slice w off (Seq.length w))

let open_eq (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (sp: perm) (count: SZ.t) (input: S.slice U8.t)
  (pm: perm) (l: list (asn1_t k))
: Lemma (PS.ml_match0 d pm (ItT.Base (ItT.Serialized sp count input)) l ==
         It.base_mixed_list_match_n (arel true d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (SZ.v count) pm
           (ItT.Serialized sp count input) l)
= assert (PS.ml_match0 d pm (ItT.Base (ItT.Serialized sp count input)) l ==
          It.base_mixed_list_match_n (arel true d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (SZ.v count) pm
            (ItT.Serialized sp count input) l)
    by (FStar.Tactics.V2.norm [delta_only [`%PS.ml_match0; `%It.mixed_list_match; `%It.mixed_list_match_n;
          `%ItT.mixed_list_length; `%ItT.base_mixed_list_length; `%ml_ops; `%IO.sizet_ops;
          `%IO.__proj__Mkint_ops__item__v]; iota; zeta; primops];
        FStar.Tactics.V2.trefl ())

#push-options "--fuel 1 --ifuel 1"
let open_nl (#s: _) (k: asn1_k s) (w: Seq.seq U8.t) (n: nat) (l_all: VC.nlist n (asn1_t k)) (l: list (asn1_t k))
: Lemma (requires LPB.pts_to_parsed_strong_prefix_prop (VC.parse_nlist n #asn1_strong_parser_kind (asn1_as_parser k)) w l_all /\
                  l == snd (List.Tot.splitAt 0 l_all))
        (ensures nl_at k w 0 n l)
= Seq.lemma_eq_elim (Seq.slice w 0 (Seq.length w)) w
#pop-options

let ser_eta (#t: Type0) (x: ml t) (sp: perm) (count: SZ.t) (input: S.slice U8.t)
: Lemma (requires is_serialized x /\ sp == ItT.Serialized?.sp (ItT.Base?._0 x) /\
                  count == ItT.Serialized?.count (ItT.Base?._0 x) /\ input == ItT.Serialized?.payload (ItT.Base?._0 x))
        (ensures x == ItT.Base (ItT.Serialized sp count input))
= ()

let open_inv (#s: _) (k: asn1_k s) (w: Seq.seq U8.t) (n: nat) (l_all: VC.nlist (0 + n) (asn1_t k)) (l: list (asn1_t k)) : prop =
  LPB.pts_to_parsed_strong_prefix_prop (VC.parse_nlist (0 + n) #asn1_strong_parser_kind (asn1_as_parser k)) w l_all /\
  l == snd (List.Tot.splitAt 0 l_all)

let mk_inv (#s: _) (k: asn1_k s) (w: Seq.seq U8.t) (n: nat) (l_all: VC.nlist (0 + n) (asn1_t k)) (l: list (asn1_t k))
: Lemma (requires LPB.pts_to_parsed_strong_prefix_prop (VC.parse_nlist (0 + n) #asn1_strong_parser_kind (asn1_as_parser k)) w l_all)
        (ensures l == snd (List.Tot.splitAt 0 l_all) ==> open_inv k w n l_all l)
= ()

ghost fn close_ser (#s: Ghost.erased (Set.set asn1_id_t)) (#k: Ghost.erased (asn1_k s)) (#t: Type0) (d: Ghost.erased (adesc k t))
  (x: ml t) (sp: perm) (count: SZ.t) (input: S.slice U8.t) (pm: perm) (w: Seq.seq U8.t)
  (l_all: VC.nlist (0 + SZ.v count) (asn1_t k)) (l: list (asn1_t k))
  requires S.pts_to input #(pm *. sp) w **
    pure (open_inv k w (SZ.v count) l_all l /\ SZ.fits (SZ.v count) /\
          x == ItT.Base (ItT.Serialized sp count input) /\ is_serialized x)
  ensures PS.ml_match d pm x l
{
  let la = l_all;
  fold (LPB.pts_to_parsed_strong_prefix (VC.parse_nlist (0 + SZ.v count) #asn1_strong_parser_kind (asn1_as_parser k)) input #(pm *. sp) la);
  fold (It.base_mixed_list_match_n (arel true d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (SZ.v count) pm
          (ItT.Serialized sp count input) l);
  open_eq d sp count input pm l;
  rewrite (It.base_mixed_list_match_n (arel true d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (SZ.v count) pm
             (ItT.Serialized sp count input) l)
       as (PS.ml_match0 d pm x l);
  fold (PS.ml_match d pm x l)
}

#push-options "--z3rlimit 40 --fuel 1 --ifuel 2 --using_facts_from '* -ASN1 -LowParse +LowParse.Spec.VCList +LowParse.Spec.Base +LowParse.PulseParse.Base +ASN1.Base +ASN1.Pulse.ParseSeqOf +ASN1.Pulse.Rel.is_serialized +LowParse.PulseParse.Iterator.Type'"
(** The serialized chunk and element count of a parsed SEQUENCE OF. *)
fn ml_open (#s: Ghost.erased (Set.set asn1_id_t)) (#k: Ghost.erased (asn1_k s)) (#t: Type0) (d: Ghost.erased (adesc k t))
  (x: ml t) (#pm: perm) (#l: Ghost.erased (list (asn1_t k)))
  requires PS.ml_match d pm x l
  returns r: (S.slice U8.t & SZ.t)
  ensures exists* (q: perm) (w: Seq.seq U8.t).
    S.pts_to (fst r) #q w ** pure (nl_at k w 0 (SZ.v (snd r)) l) **
    trade (S.pts_to (fst r) #q w) (PS.ml_match d pm x l)
{
  unfold (PS.ml_match d pm x l);
  let b = ItT.Base?._0 x;
  let count = ItT.Serialized?.count b;
  let input = ItT.Serialized?.payload b;
  let sp : Ghost.erased perm = ItT.Serialized?.sp b;
  ser_eta x sp count input;
  rewrite (PS.ml_match0 d pm x l) as (PS.ml_match0 d pm (ItT.Base (ItT.Serialized sp count input)) l);
  open_eq d sp count input pm l;
  rewrite (PS.ml_match0 d pm (ItT.Base (ItT.Serialized sp count input)) l)
       as (It.base_mixed_list_match_n (arel true d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (SZ.v count) pm
             (ItT.Serialized sp count input) l);
  unfold (It.base_mixed_list_match_n (arel true d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (SZ.v count) pm
            (ItT.Serialized sp count input) l);
  with l_all. unfold (LPB.pts_to_parsed_strong_prefix (VC.parse_nlist (0 + SZ.v count) #asn1_strong_parser_kind (asn1_as_parser k)) input #(pm *. sp) l_all);
  with w. assert (S.pts_to input #(pm *. sp) w);
  open_nl k w (SZ.v count) l_all l;
  mk_inv k w (SZ.v count) l_all l;
  assert (pure (open_inv k w (SZ.v count) l_all l));
  intro_trade (S.pts_to input #(pm *. sp) w) (PS.ml_match d pm x l)
    (pure (open_inv k w (SZ.v count) l_all l /\ SZ.fits (SZ.v count) /\
           x == ItT.Base (ItT.Serialized sp count input) /\ is_serialized x)) fn _ {
    close_ser d x sp count input pm w l_all l
  };
  (input, count)
}
#pop-options

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let nl_step_lemma (#s: _) (k: asn1_k s) (w: Seq.seq U8.t) (off: SZ.t) (n: nat) (l: list (asn1_t k))
  (off': SZ.t) (ok: bool)
: Lemma (requires nl_at k w (SZ.v off) (n + 1) l /\
                  LPS.validator_postcond #asn1_strong_parser_kind (asn1_as_parser k) off w off' ok)
        (ensures ok /\ Cons? l /\ SZ.v off <= SZ.v off' /\ SZ.v off' <= Seq.length w /\
                 PP.parsed #asn1_strong_parser_kind (asn1_as_parser k) (Seq.slice w (SZ.v off) (SZ.v off')) (List.Tot.hd l) /\
                 nl_at k w (SZ.v off') n (List.Tot.tl l))
= let p : LP.parser asn1_strong_parser_kind (asn1_t k) = asn1_as_parser k in
  let b = Seq.slice w (SZ.v off) (Seq.length w) in
  VC.parse_nlist_eq (n + 1) #asn1_strong_parser_kind p b;
  let Some (hd, c1) = LP.parse p b in
  let e = Seq.slice w (SZ.v off) (SZ.v off + c1) in
  assert (Seq.slice b 0 c1 `Seq.equal` Seq.slice e 0 c1);
  LP.parse_strong_prefix p b e;
  assert (PP.parsed #asn1_strong_parser_kind p e hd);
  assert (Seq.slice b c1 (Seq.length b) `Seq.equal` Seq.slice w (SZ.v off + c1) (Seq.length w))

#pop-options

(** The end of the element at [off]. *)
inline_for_extraction noextract
fn nl_step (#s: Ghost.erased (Set.set asn1_id_t)) (#k: Ghost.erased (asn1_k s))
  (vd: LPS.validator #(asn1_t k) #asn1_strong_parser_kind (asn1_as_parser k))
  (input: S.slice U8.t) (off: SZ.t) (n: Ghost.erased nat)
  (#q: perm) (#w: Ghost.erased (Seq.seq U8.t)) (#l: Ghost.erased (list (asn1_t k)))
  requires S.pts_to input #q w ** pure (nl_at k w (SZ.v off) (n + 1) l)
  returns off': SZ.t
  ensures S.pts_to input #q w **
          pure (Cons? l /\ SZ.v off <= SZ.v off' /\ SZ.v off' <= Seq.length w /\
                PP.parsed #asn1_strong_parser_kind (asn1_as_parser k) (Seq.slice w (SZ.v off) (SZ.v off')) (List.Tot.hd l) /\
                nl_at k w (SZ.v off') n (List.Tot.tl l))
{
  let mut poff = off;
  let ok = vd input poff;
  let off' = !poff;
  nl_step_lemma k w off n l off' ok;
  off'
}

(** The element at [off], parsed, and the end of it. *)
inline_for_extraction noextract
fn nl_elem (#s: Ghost.erased (Set.set asn1_id_t)) (#k: Ghost.erased (asn1_k s)) (#t: Type0) (#d: Ghost.erased (adesc k t))
  (vd: LPS.validator #(asn1_t k) #asn1_strong_parser_kind (asn1_as_parser k))
  (pa: PP.aparser #t #(asn1_t k) (arel true d) #asn1_strong_parser_kind (asn1_as_parser k))
  (input: S.slice U8.t) (off: SZ.t) (n: Ghost.erased nat)
  (#q: perm) (#w: Ghost.erased (Seq.seq U8.t)) (#l: Ghost.erased (list (asn1_t k)))
  requires S.pts_to input #q w ** pure (nl_at k w (SZ.v off) (n + 1) l)
  returns r: (t & SZ.t)
  ensures exists* (h: asn1_t k).
          arel true d q (fst r) h **
          trade (arel true d q (fst r) h) (S.pts_to input #q w) **
          pure (Cons? l /\ h == List.Tot.hd l /\ SZ.v off <= SZ.v (snd r) /\ nl_at k w (SZ.v (snd r)) n (List.Tot.tl l))
{
  let off' = nl_step #s #k vd input off n #q #w #l;
  let h : Ghost.erased (asn1_t k) = List.Tot.hd l;
  let sub = SU.subslice_trade input off off';
  let x = pa sub #q #(Seq.slice w (SZ.v off) (SZ.v off')) #h;
  trade_compose (arel true d q x h) (S.pts_to sub #q (Seq.slice w (SZ.v off) (SZ.v off'))) (S.pts_to input #q w);
  (x, off')
}

(** {2 Bytes} *)

(** Copy [src] into the front of [dst], if it fits. *)
fn copy_slice (src: S.slice U8.t) (#pm: perm) (#w: Ghost.erased (Seq.seq U8.t))
  (dst: A.array U8.t) (dlen: SZ.t) (#old: Ghost.erased (Seq.seq U8.t))
  requires S.pts_to src #pm w ** A.pts_to dst old ** pure (A.length dst == SZ.v dlen)
  returns n: SZ.t
  ensures S.pts_to src #pm w ** (exists* d. A.pts_to dst d **
          pure (Seq.length d == Seq.length old /\
                (SZ.v n <= Seq.length d) /\
                (SZ.v n > 0 \/ Seq.length w == 0 ==> Seq.slice d 0 (SZ.v n) == reveal w) /\
                (SZ.v n == 0 ==> Seq.length w == 0 \/ Seq.length w > Seq.length d)))
{
  S.pts_to_len src;
  A.pts_to_len dst;
  let len = S.len src;
  if (SZ.lte len dlen) {
    let mut i = 0sz;
    while (let vi = !i; SZ.lt vi len)
    invariant exists* (vi: SZ.t) (d: Seq.seq U8.t).
      pts_to i vi ** A.pts_to dst d ** S.pts_to src #pm w **
      pure (SZ.v vi <= SZ.v len /\ Seq.length d == Seq.length old /\
            (forall (j: nat). j < SZ.v vi ==> Seq.index d j == Seq.index w j))
    decreases (SZ.v len - SZ.v (!i))
    {
      let vi = !i;
      let x = S.(src.(vi));
      dst.(vi) <- x;
      i := SZ.add vi 1sz;
    };
    with d. assert (A.pts_to dst d);
    assert (pure (Seq.slice d 0 (SZ.v len) `Seq.equal` reveal w));

    len
  } else {
    0sz
  }
}

(** Whether two slices hold the same bytes. *)
fn slice_eq (a: S.slice U8.t) (#pa: perm) (#wa: Ghost.erased (Seq.seq U8.t))
  (b: S.slice U8.t) (#pb: perm) (#wb: Ghost.erased (Seq.seq U8.t))
  requires S.pts_to a #pa wa ** S.pts_to b #pb wb
  returns r: bool
  ensures S.pts_to a #pa wa ** S.pts_to b #pb wb ** pure (r <==> reveal wa == reveal wb)
{
  S.pts_to_len a;
  S.pts_to_len b;
  if (S.len a = S.len b) {
    let n = S.len a;
    let mut i = 0sz;
    let mut ok = true;
    while (let vi = !i; let vok = !ok; (vok && SZ.lt vi n))
    invariant exists* (vi: SZ.t) (vok: bool).
      pts_to i vi ** pts_to ok vok ** S.pts_to a #pa wa ** S.pts_to b #pb wb **
      pure (SZ.v vi <= SZ.v n /\
            (vok ==> (forall (j: nat). j < SZ.v vi ==> Seq.index wa j == Seq.index wb j)) /\
            (not vok ==> reveal wa =!= reveal wb))
    decreases ((if !ok then 1 else 0) + SZ.v n - SZ.v (!i))
    {
      let vi = !i;
      let x = S.(a.(vi));
      let y = S.(b.(vi));
      if (x = y) {
        i := SZ.add vi 1sz;
      } else {
        assert (pure (Seq.index wa (SZ.v vi) =!= Seq.index wb (SZ.v vi)));
        ok := false;
      }
    };
    let vok = !ok;
    if vok {
      assert (pure (Seq.equal wa wb));
      true
    } else {
      false
    }
  } else {
    false
  }
}

(** {2 Whole buffers} *)

let whole_lemma (#s: _) (k: asn1_k s) (w: Seq.seq U8.t) (off: SZ.t) (ok: bool)
: Lemma (requires LPS.validator_postcond #asn1_strong_parser_kind (asn1_as_parser k) 0sz w off ok)
        (ensures (if ok && SZ.v off = Seq.length w
                  then Some? (XP.parse_full k w) /\
                       PP.parsed #asn1_strong_parser_kind (asn1_as_parser k) w (Some?.v (XP.parse_full k w))
                  else XP.parse_full k w == None))
= assert (Seq.equal (Seq.slice w 0 (Seq.length w)) w)

let whole_res (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (q: perm) (input: S.slice U8.t)
  (w: Seq.seq U8.t) (r: option t) : slprop =
  match r with
  | None -> S.pts_to input #q w ** pure (XP.parse_full k w == None)
  | Some x -> exists* (v: asn1_t k). arel true d q x v ** trade (arel true d q x v) (S.pts_to input #q w) **
             pure (XP.parse_full k w == Some v)

(** Parse all of [input] as one [k]. *)
inline_for_extraction noextract
fn open_whole (#s: Ghost.erased (Set.set asn1_id_t)) (#k: Ghost.erased (asn1_k s)) (#t: Type0) (#d: Ghost.erased (adesc k t))
  (vd: LPS.validator #(asn1_t k) #asn1_strong_parser_kind (asn1_as_parser k))
  (pa: PP.aparser #t #(asn1_t k) (arel true d) #asn1_strong_parser_kind (asn1_as_parser k))
  (input: S.slice U8.t) (#q: perm) (#w: Ghost.erased (Seq.seq U8.t))
  requires S.pts_to input #q w
  returns r: option t
  ensures whole_res d q input w r
{
  S.pts_to_len input;
  let mut poff = 0sz;
  let ok = vd input poff;
  let off = !poff;
  whole_lemma k w off ok;
  if (ok && off = S.len input) {
    let v : Ghost.erased (asn1_t k) = Some?.v (XP.parse_full k w);
    let x = pa input #q #w #v;
    fold (whole_res d q input w (Some x));
    Some x
  } else {
    fold (whole_res d q input w None);
    None #t
  }
}
