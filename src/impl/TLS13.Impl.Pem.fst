module TLS13.Impl.Pem

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module A = Pulse.Lib.Array
module AC = TLS13.Impl.ArrayCopy
module B = TLS13.Bytes
module Cast = FStar.Int.Cast
module S = TLS13.Pem.Spec
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module U8 = FStar.UInt8

(** ** Search *)

fn region_eq
  (a:array U8.t) (#pa:perm) (#sa:Ghost.erased B.bytes) (ai:SZ.t)
  (b:array U8.t) (#pb:perm) (#sb:Ghost.erased B.bytes) (bi:SZ.t)
  (n:SZ.t)
  requires pts_to a #pa sa ** pts_to b #pb sb **
           pure (SZ.v ai + SZ.v n <= Seq.length sa /\
                 SZ.v bi + SZ.v n <= Seq.length sb)
  returns r:bool
  ensures pts_to a #pa sa ** pts_to b #pb sb **
          pure (SZ.v ai + SZ.v n <= Seq.length sa /\
                SZ.v bi + SZ.v n <= Seq.length sb /\
                r == S.region_eq sa (SZ.v ai) sb (SZ.v bi) (SZ.v n))
{
  A.pts_to_len a;
  A.pts_to_len b;
  let mut k = 0sz;
  let mut ok = true;
  while (let vok = !ok; let vk = !k; (vok && SZ.lt vk n))
  invariant exists* (vk:SZ.t) (vok:bool).
    pts_to k vk ** pts_to ok vok ** pts_to a #pa sa ** pts_to b #pb sb **
    pure (SZ.v vk <= SZ.v n /\
          S.region_eq sa (SZ.v ai) sb (SZ.v bi) (SZ.v n) ==
            (vok && S.region_eq sa (SZ.v ai + SZ.v vk) sb (SZ.v bi + SZ.v vk)
                                  (SZ.v n - SZ.v vk)))
  decreases (SZ.v n - SZ.v !k)
  {
    let vk = !k;
    let x = a.(SZ.add ai vk);
    let y = b.(SZ.add bi vk);
    ok := (x = y);
    k := SZ.add vk 1sz;
  };
  !ok
}

let opt_nat (r:option SZ.t) : option nat =
  match r with
  | Some i -> Some (SZ.v i)
  | None -> None

let find_spec (h needle:B.bytes) (from:nat) : option nat =
  match S.find_from h needle from with
  | Some i -> Some i
  | None -> None

let lemma_region_eq_append
  (h:B.bytes) (i:nat) (p:B.bytes) (lo:nat) (ll:nat)
  : Lemma
    (requires i + Seq.length p + ll <= Seq.length h /\ lo + ll <= Seq.length h)
    (ensures
      S.region_eq h i (Seq.append p (Seq.slice h lo (lo + ll))) 0 (Seq.length p + ll) ==
        (S.region_eq h i p 0 (Seq.length p) &&
         S.region_eq h (i + Seq.length p) h lo ll))
  = let q = Seq.append p (Seq.slice h lo (lo + ll)) in
    S.region_eq_iff h i q 0 (Seq.length p + ll);
    S.region_eq_iff h i p 0 (Seq.length p);
    S.region_eq_iff h (i + Seq.length p) h lo ll;
    let np = Seq.length p in
    let sl = Seq.slice h lo (lo + ll) in
    let aux (k:nat{k < np + ll})
      : Lemma (Seq.index q k == (if k < np then Seq.index p k else Seq.index h (lo + (k - np))))
      = if k < np then Seq.lemma_index_app1 p sl k
        else Seq.lemma_index_app2 p sl k
    in
    FStar.Classical.forall_intro aux;
    introduce (forall (k:nat). k < np + ll ==> Seq.index h (i + k) == Seq.index q (0 + k)) ==>
              ((forall (k:nat). k < np ==> Seq.index h (i + k) == Seq.index p (0 + k)) /\
               (forall (k:nat). k < ll ==> Seq.index h (i + np + k) == Seq.index h (lo + k)))
    with begin
      introduce forall (k:nat). k < np ==> Seq.index h (i + k) == Seq.index p (0 + k)
      with introduce _ ==> _
      with eliminate forall (k:nat). k < np + ll ==> Seq.index h (i + k) == Seq.index q (0 + k) with k;
      introduce forall (k:nat). k < ll ==> Seq.index h (i + np + k) == Seq.index h (lo + k)
      with introduce _ ==> _
      with begin
        eliminate forall (k:nat). k < np + ll ==> Seq.index h (i + k) == Seq.index q (0 + k) with (np + k);
        aux (np + k)
      end
    end;
    introduce ((forall (k:nat). k < np ==> Seq.index h (i + k) == Seq.index p (0 + k)) /\
               (forall (k:nat). k < ll ==> Seq.index h (i + np + k) == Seq.index h (lo + k))) ==>
              (forall (k:nat). k < np + ll ==> Seq.index h (i + k) == Seq.index q (0 + k))
    with introduce forall (k:nat). k < np + ll ==> Seq.index h (i + k) == Seq.index q (0 + k)
    with introduce _ ==> _
    with begin
      aux k;
      if k < np
      then eliminate forall (k:nat). k < np ==> Seq.index h (i + k) == Seq.index p (0 + k) with k
      else eliminate forall (k:nat). k < ll ==> Seq.index h (i + np + k) == Seq.index h (lo + k) with (k - np)
    end

(** The first occurrence at or after [from] of [needle] followed by
    [h[lab, lab + lab_len)]. *)
fn find
  (h:array U8.t) (#sh:Ghost.erased B.bytes) (h_len:SZ.t) (from:SZ.t)
  (needle:array U8.t) (#sn:Ghost.erased B.bytes) (n_len:SZ.t)
  (lab:SZ.t) (lab_len:SZ.t)
  requires pts_to h sh ** pts_to needle sn **
           pure (Seq.length sh == SZ.v h_len /\
                 Seq.length sn == SZ.v n_len /\
                 SZ.v n_len > 0 /\
                 SZ.v from <= SZ.v h_len /\
                 SZ.v lab + SZ.v lab_len <= SZ.v h_len)
  returns r:option SZ.t
  ensures pts_to h sh ** pts_to needle sn **
          pure (SZ.v lab + SZ.v lab_len <= Seq.length sh /\
                opt_nat r ==
                find_spec sh
                  (Seq.append sn (Seq.slice sh (SZ.v lab) (SZ.v lab + SZ.v lab_len)))
                  (SZ.v from))
{
  A.pts_to_len h;
  let full = Ghost.hide (Seq.append sn (Seq.slice sh (SZ.v lab) (SZ.v lab + SZ.v lab_len)));
  let fits = (SZ.lte n_len h_len && SZ.lte lab_len (SZ.sub h_len n_len));
  if (not fits) {
    (* The needle is longer than the haystack. *)
    None #SZ.t
  } else {
    let full_len = SZ.add n_len lab_len;
    let last_i = SZ.sub h_len full_len;
    let mut i = from;
    let mut found = false;
    while (let vf = !found; let vi = !i; (not vf && SZ.lte vi last_i))
    invariant exists* (vi:SZ.t) (vf:bool).
      pts_to i vi ** pts_to found vf ** pts_to h sh ** pts_to needle sn **
      pure (SZ.v from <= SZ.v vi /\ SZ.v vi <= SZ.v h_len /\
            (vf ==> SZ.v vi <= SZ.v last_i) /\
            find_spec sh full (SZ.v from) ==
              (if vf then Some (SZ.v vi) else find_spec sh full (SZ.v vi)))
    decreases (if !found then 0 else SZ.v h_len + 1 - SZ.v !i)
    {
      let vi = !i;
      let m1 = region_eq h vi needle 0sz n_len;
      if m1 {
        A.share h;
        let m2 = region_eq h (SZ.add vi n_len) h lab lab_len;
        A.gather h;
        lemma_region_eq_append sh (SZ.v vi) sn (SZ.v lab) (SZ.v lab_len);
        if m2 {
          found := true;
        } else {
          i := SZ.add vi 1sz;
        }
      } else {
        lemma_region_eq_append sh (SZ.v vi) sn (SZ.v lab) (SZ.v lab_len);
        i := SZ.add vi 1sz;
      }
    };
    let vf = !found;
    if vf {
      let vi = !i;
      Some vi
    } else {
      None #SZ.t
    }
  }
}

(** [find] for a needle on its own. *)
fn find_needle
  (h:array U8.t) (#sh:Ghost.erased B.bytes) (h_len:SZ.t) (from:SZ.t)
  (needle:array U8.t) (#sn:Ghost.erased B.bytes) (n_len:SZ.t)
  requires pts_to h sh ** pts_to needle sn **
           pure (Seq.length sh == SZ.v h_len /\
                 Seq.length sn == SZ.v n_len /\
                 SZ.v n_len > 0 /\
                 SZ.v from <= SZ.v h_len)
  returns r:option SZ.t
  ensures pts_to h sh ** pts_to needle sn **
          pure (opt_nat r == find_spec sh sn (SZ.v from))
{
  let r = find h h_len from needle n_len 0sz 0sz;
  assert (pure (Seq.equal (Seq.append sn (Seq.slice sh 0 0)) sn));
  r
}

fn find_byte
  (h:array U8.t) (#sh:Ghost.erased B.bytes) (h_len:SZ.t) (c:U8.t) (from:SZ.t)
  requires pts_to h sh **
           pure (Seq.length sh == SZ.v h_len /\ SZ.v from <= SZ.v h_len)
  returns r:option SZ.t
  ensures pts_to h sh **
          pure (SZ.v from <= Seq.length sh /\
                opt_nat r ==
                (match S.find_byte sh c (SZ.v from) with
                 | Some i -> Some i
                 | None -> None))
{
  A.pts_to_len h;
  let mut i = from;
  let mut found = false;
  while (let vf = !found; let vi = !i; (not vf && SZ.lt vi h_len))
  invariant exists* (vi:SZ.t) (vf:bool).
    pts_to i vi ** pts_to found vf ** pts_to h sh **
    pure (SZ.v from <= SZ.v vi /\ SZ.v vi <= SZ.v h_len /\
          (vf ==> SZ.v vi < SZ.v h_len) /\
          (match S.find_byte sh c (SZ.v from) with
           | Some j -> Some j
           | None -> None) ==
          (if vf then Some (SZ.v vi)
           else (match S.find_byte sh c (SZ.v vi) with
                 | Some j -> Some j
                 | None -> None)))
  decreases (if !found then 0 else SZ.v h_len + 1 - SZ.v !i)
  {
    let vi = !i;
    let x = h.(vi);
    if (x = c) {
      found := true;
    } else {
      i := SZ.add vi 1sz;
    }
  };
  let vf = !found;
  if vf {
    let vi = !i;
    Some vi
  } else {
    None #SZ.t
  }
}

fn strip_cr
  (h:array U8.t) (#sh:Ghost.erased B.bytes) (lo hi:SZ.t)
  requires pts_to h sh **
           pure (SZ.v lo <= SZ.v hi /\ SZ.v hi <= Seq.length sh)
  returns r:SZ.t
  ensures pts_to h sh **
          pure (SZ.v lo <= SZ.v hi /\ SZ.v hi <= Seq.length sh /\
                SZ.v r == S.strip_cr sh (SZ.v lo) (SZ.v hi))
{
  let mut j = hi;
  let mut go = true;
  while (!go)
  invariant exists* (vj:SZ.t) (vg:bool).
    pts_to j vj ** pts_to go vg ** pts_to h sh **
    pure (SZ.v lo <= SZ.v vj /\ SZ.v vj <= SZ.v hi /\
          S.strip_cr sh (SZ.v lo) (SZ.v hi) ==
            (if vg then S.strip_cr sh (SZ.v lo) (SZ.v vj) else SZ.v vj))
  decreases (if !go then SZ.v !j + 1 else 0)
  {
    let vj = !j;
    if (SZ.gt vj lo) {
      let x = h.(SZ.sub vj 1sz);
      if (x = 13uy) {
        j := SZ.sub vj 1sz;
      } else {
        go := false;
      }
    } else {
      go := false;
    }
  };
  !j
}

(** ** Base64 *)

let b64_result (spec:option B.bytes) (out:B.bytes) (off:nat) (r:option SZ.t) : prop =
  match spec, r with
  | None, None -> True
  | Some d, Some n ->
    off + SZ.v n <= Seq.length out /\ Seq.slice out off (off + SZ.v n) == d
  | _ -> False

let lemma_pow2_bits (b:nat{b < 8}) : Lemma (pow2 b <= 128 /\ pow2 (b + 6) == pow2 b * 64) =
  FStar.Math.Lemmas.pow2_le_compat 7 b;
  FStar.Math.Lemmas.pow2_plus b 6

#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"
(** Decodes the base64 text [src[lo, hi)] into [out] from [off]. *)
fn b64_decode_into
  (src:array U8.t) (#ss:Ghost.erased B.bytes) (lo hi:SZ.t)
  (out:array U8.t) (#so:Ghost.erased B.bytes) (off:SZ.t)
  requires pts_to src ss ** pts_to out so **
           pure (SZ.v lo <= SZ.v hi /\ SZ.v hi <= Seq.length ss /\
                 SZ.v off + (SZ.v hi - SZ.v lo) <= Seq.length so)
  returns r:option SZ.t
  ensures exists* so'.
          pts_to src ss ** pts_to out so' **
          pure (SZ.v lo <= SZ.v hi /\ SZ.v hi <= Seq.length ss /\
                SZ.v off <= Seq.length so /\
                Seq.length so' == Seq.length so /\
                Seq.slice so' 0 (SZ.v off) == Seq.slice so 0 (SZ.v off) /\
                b64_result (S.b64_decode (Seq.slice ss (SZ.v lo) (SZ.v hi)))
                  so' (SZ.v off) r /\
                (Some? r ==> SZ.v (Some?.v r) <= SZ.v hi - SZ.v lo))
{
  A.pts_to_len src;
  A.pts_to_len out;
  let s = Ghost.hide (Seq.slice ss (SZ.v lo) (SZ.v hi));
  let n = SZ.sub hi lo;
  let mut i = 0sz;
  let mut acc = 0ul;
  let mut bits = 0ul;
  let mut pad = 0sz;
  let mut len = 0sz;
  let mut ok = true;
  assert (pure (Seq.equal (Seq.slice so (SZ.v off) (SZ.v off + 0)) Seq.empty));
  while (let vok = !ok; let vi = !i; (vok && SZ.lt vi n))
  invariant exists* (vi:SZ.t) (vacc:U32.t) (vbits:U32.t) (vpad:SZ.t) (vlen:SZ.t)
                    (vok:bool) (o:B.bytes).
    pts_to i vi ** pts_to acc vacc ** pts_to bits vbits ** pts_to pad vpad **
    pts_to len vlen ** pts_to ok vok ** pts_to src ss ** pts_to out o **
    pure (SZ.v vi <= SZ.v n /\ SZ.v vlen <= SZ.v vi /\ SZ.v vpad <= SZ.v vi /\
          U32.v vbits < 8 /\ U32.v vacc < pow2 (U32.v vbits) /\
          Seq.length o == Seq.length so /\
          Seq.slice o 0 (SZ.v off) == Seq.slice so 0 (SZ.v off) /\
          S.b64_decode s ==
            (if vok
             then S.b64_go s (SZ.v vi) (U32.v vacc) (U32.v vbits) (SZ.v vpad)
                    (Seq.slice o (SZ.v off) (SZ.v off + SZ.v vlen))
             else None))
  decreases (SZ.v n - SZ.v !i)
  {
    let vi = !i;
    let c = src.(SZ.add lo vi);
    if (S.is_whitespace c) {
      i := SZ.add vi 1sz;
    } else if (c = S.pad_char) {
      let vpad = !pad;
      pad := SZ.add vpad 1sz;
      i := SZ.add vi 1sz;
    } else {
      let value = S.b64_value c;
      let vpad = !pad;
      if (None? value || vpad <> 0sz) {
        ok := false;
        i := SZ.add vi 1sz;
      } else {
        let v = Some?.v value;
        let vacc = !acc;
        let vbits = !bits;
        lemma_pow2_bits (U32.v vbits);
        let acc1 = U32.add (U32.mul vacc 64ul) (Cast.uint8_to_uint32 v);
        let bits1 = U32.add vbits 6ul;
        if (U32.gte bits1 8ul) {
          let sh = U32.sub bits1 8ul;
          FStar.Math.Lemmas.pow2_lt_compat 32 (U32.v sh);
          FStar.Math.Lemmas.small_mod (pow2 (U32.v sh)) (pow2 32);
          let d = U32.shift_left 1ul sh;
          assert (pure (U32.v d == pow2 (U32.v sh)));
          let byte = Cast.uint32_to_uint8 (U32.div acc1 d);
          let vlen = !len;
          with o. assert (pts_to out o);
          out.(SZ.add off vlen) <- byte;
          with o'. assert (pts_to out o');
          assert (pure (Seq.equal (Seq.slice o' 0 (SZ.v off)) (Seq.slice o 0 (SZ.v off))));
          assert (pure (Seq.equal
            (Seq.slice o' (SZ.v off) (SZ.v off + SZ.v vlen + 1))
            (Seq.snoc (Seq.slice o (SZ.v off) (SZ.v off + SZ.v vlen))
               (U8.uint_to_t ((U32.v acc1 / pow2 (U32.v sh)) % 256)))));
          len := SZ.add vlen 1sz;
          acc := U32.rem acc1 d;
          bits := sh;
          i := SZ.add vi 1sz;
        } else {
          acc := acc1;
          bits := bits1;
          i := SZ.add vi 1sz;
        }
      }
    }
  };
  let vok = !ok;
  let vpad = !pad;
  let vbits = !bits;
  if (not vok || SZ.gt vpad 2sz || U32.gte vbits 6ul) {
    None #SZ.t
  } else {
    let vlen = !len;
    Some vlen
  }
}
#pop-options

(** ** Needles *)

(** [s] agrees with [t] on its first [k] bytes. *)
let prefix_ok (s t:Seq.seq U8.t) (k:nat) : prop =
  Seq.length s == Seq.length t /\ k <= Seq.length t /\
  (forall (i:nat). i < k ==> Seq.index s i == Seq.index t i)

let prefix_ok_full (s t:Seq.seq U8.t)
  : Lemma (requires prefix_ok s t (Seq.length t)) (ensures s == t)
  = Seq.lemma_eq_intro s t

(** Write byte [k] of the constant [t]; the history of earlier writes is
    summarised by [prefix_ok] so each step is a local proof. *)
inline_for_extraction
fn write_at (a:array U8.t) (t:Ghost.erased (Seq.seq U8.t)) (k:SZ.t) (c:U8.t)
            (#s:Ghost.erased (Seq.seq U8.t))
  requires pts_to a s **
           pure (prefix_ok s t (SZ.v k) /\ SZ.v k < Seq.length t /\
                 c == Seq.index t (SZ.v k))
  ensures exists* s'. pts_to a s' ** pure (prefix_ok s' t (SZ.v k + 1))
{
  A.pts_to_len a;
  a.(k) <- c
}

inline_for_extraction
fn write_cert_begin (a:array U8.t)
  requires pts_to a (Seq.create 27 0uy)
  ensures pts_to a S.cert_begin
{
  S.cert_begin_bytes ();
  write_at a S.cert_begin 0sz 45uy;
  write_at a S.cert_begin 1sz 45uy;
  write_at a S.cert_begin 2sz 45uy;
  write_at a S.cert_begin 3sz 45uy;
  write_at a S.cert_begin 4sz 45uy;
  write_at a S.cert_begin 5sz 66uy;
  write_at a S.cert_begin 6sz 69uy;
  write_at a S.cert_begin 7sz 71uy;
  write_at a S.cert_begin 8sz 73uy;
  write_at a S.cert_begin 9sz 78uy;
  write_at a S.cert_begin 10sz 32uy;
  write_at a S.cert_begin 11sz 67uy;
  write_at a S.cert_begin 12sz 69uy;
  write_at a S.cert_begin 13sz 82uy;
  write_at a S.cert_begin 14sz 84uy;
  write_at a S.cert_begin 15sz 73uy;
  write_at a S.cert_begin 16sz 70uy;
  write_at a S.cert_begin 17sz 73uy;
  write_at a S.cert_begin 18sz 67uy;
  write_at a S.cert_begin 19sz 65uy;
  write_at a S.cert_begin 20sz 84uy;
  write_at a S.cert_begin 21sz 69uy;
  write_at a S.cert_begin 22sz 45uy;
  write_at a S.cert_begin 23sz 45uy;
  write_at a S.cert_begin 24sz 45uy;
  write_at a S.cert_begin 25sz 45uy;
  write_at a S.cert_begin 26sz 45uy;
  with s. assert (pts_to a s);
  prefix_ok_full s S.cert_begin;
  rewrite pts_to a s as pts_to a S.cert_begin
}

inline_for_extraction
fn write_cert_end (a:array U8.t)
  requires pts_to a (Seq.create 25 0uy)
  ensures pts_to a S.cert_end
{
  S.cert_end_bytes ();
  write_at a S.cert_end 0sz 45uy;
  write_at a S.cert_end 1sz 45uy;
  write_at a S.cert_end 2sz 45uy;
  write_at a S.cert_end 3sz 45uy;
  write_at a S.cert_end 4sz 45uy;
  write_at a S.cert_end 5sz 69uy;
  write_at a S.cert_end 6sz 78uy;
  write_at a S.cert_end 7sz 68uy;
  write_at a S.cert_end 8sz 32uy;
  write_at a S.cert_end 9sz 67uy;
  write_at a S.cert_end 10sz 69uy;
  write_at a S.cert_end 11sz 82uy;
  write_at a S.cert_end 12sz 84uy;
  write_at a S.cert_end 13sz 73uy;
  write_at a S.cert_end 14sz 70uy;
  write_at a S.cert_end 15sz 73uy;
  write_at a S.cert_end 16sz 67uy;
  write_at a S.cert_end 17sz 65uy;
  write_at a S.cert_end 18sz 84uy;
  write_at a S.cert_end 19sz 69uy;
  write_at a S.cert_end 20sz 45uy;
  write_at a S.cert_end 21sz 45uy;
  write_at a S.cert_end 22sz 45uy;
  write_at a S.cert_end 23sz 45uy;
  write_at a S.cert_end 24sz 45uy;
  with s. assert (pts_to a s);
  prefix_ok_full s S.cert_end;
  rewrite pts_to a s as pts_to a S.cert_end
}

inline_for_extraction
fn write_key_begin (a:array U8.t)
  requires pts_to a (Seq.create 11 0uy)
  ensures pts_to a S.key_begin
{
  S.key_begin_bytes ();
  write_at a S.key_begin 0sz 45uy;
  write_at a S.key_begin 1sz 45uy;
  write_at a S.key_begin 2sz 45uy;
  write_at a S.key_begin 3sz 45uy;
  write_at a S.key_begin 4sz 45uy;
  write_at a S.key_begin 5sz 66uy;
  write_at a S.key_begin 6sz 69uy;
  write_at a S.key_begin 7sz 71uy;
  write_at a S.key_begin 8sz 73uy;
  write_at a S.key_begin 9sz 78uy;
  write_at a S.key_begin 10sz 32uy;
  with s. assert (pts_to a s);
  prefix_ok_full s S.key_begin;
  rewrite pts_to a s as pts_to a S.key_begin
}

inline_for_extraction
fn write_key_suffix (a:array U8.t)
  requires pts_to a (Seq.create 16 0uy)
  ensures pts_to a S.key_suffix
{
  S.key_suffix_bytes ();
  write_at a S.key_suffix 0sz 80uy;
  write_at a S.key_suffix 1sz 82uy;
  write_at a S.key_suffix 2sz 73uy;
  write_at a S.key_suffix 3sz 86uy;
  write_at a S.key_suffix 4sz 65uy;
  write_at a S.key_suffix 5sz 84uy;
  write_at a S.key_suffix 6sz 69uy;
  write_at a S.key_suffix 7sz 32uy;
  write_at a S.key_suffix 8sz 75uy;
  write_at a S.key_suffix 9sz 69uy;
  write_at a S.key_suffix 10sz 89uy;
  write_at a S.key_suffix 11sz 45uy;
  write_at a S.key_suffix 12sz 45uy;
  write_at a S.key_suffix 13sz 45uy;
  write_at a S.key_suffix 14sz 45uy;
  write_at a S.key_suffix 15sz 45uy;
  with s. assert (pts_to a s);
  prefix_ok_full s S.key_suffix;
  rewrite pts_to a s as pts_to a S.key_suffix
}

inline_for_extraction
fn write_key_end (a:array U8.t)
  requires pts_to a (Seq.create 9 0uy)
  ensures pts_to a S.key_end
{
  S.key_end_bytes ();
  write_at a S.key_end 0sz 45uy;
  write_at a S.key_end 1sz 45uy;
  write_at a S.key_end 2sz 45uy;
  write_at a S.key_end 3sz 45uy;
  write_at a S.key_end 4sz 45uy;
  write_at a S.key_end 5sz 69uy;
  write_at a S.key_end 6sz 78uy;
  write_at a S.key_end 7sz 68uy;
  write_at a S.key_end 8sz 32uy;
  with s. assert (pts_to a s);
  prefix_ok_full s S.key_end;
  rewrite pts_to a s as pts_to a S.key_end
}


(** ** Entry points *)

(** [S.decode_body] into [out] at [off]. *)
inline_for_extraction
fn decode_body_into
  (src:array U8.t) (lo hi:SZ.t) (out:array U8.t) (off:SZ.t)
  (#ss #so:Ghost.erased B.bytes)
  requires pts_to src ss ** pts_to out so **
           pure (SZ.v lo <= SZ.v hi /\ SZ.v hi <= Seq.length ss /\
                 SZ.v off + (SZ.v hi - SZ.v lo) <= Seq.length so)
  returns r:option SZ.t
  ensures exists* so'.
          pts_to src ss ** pts_to out so' **
          pure (SZ.v lo <= SZ.v hi /\ SZ.v hi <= Seq.length ss /\
                SZ.v off <= Seq.length so /\
                Seq.length so' == Seq.length so /\
                Seq.slice so' 0 (SZ.v off) == Seq.slice so 0 (SZ.v off) /\
                b64_result (S.decode_body ss (SZ.v lo) (SZ.v hi)) so' (SZ.v off) r /\
                (Some? r ==> SZ.v (Some?.v r) <= SZ.v hi - SZ.v lo))
{
  let r = b64_decode_into src lo hi out off;
  match r {
    None -> { None #SZ.t }
    Some n -> {
      if (n = 0sz) {
        with o. assert (pts_to out o);
        assert (pure (Seq.length (Seq.slice o (SZ.v off) (SZ.v off + 0)) == 0));
        None #SZ.t
      } else {
        Some n
      }
    }
  }
}

#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"
fn certificates_to_der
  (pem:array U8.t)
  (pem_len:SZ.t)
  (out:array U8.t)
  requires pts_to pem 'pem_bytes **
           pts_to out 'out_bytes **
           pure (Seq.length 'pem_bytes == SZ.v pem_len /\
                 Seq.length 'out_bytes == SZ.v pem_len)
  returns r:option SZ.t
  ensures exists* out_bytes.
          pts_to pem 'pem_bytes **
          pts_to out out_bytes **
          pure (Seq.length out_bytes == SZ.v pem_len /\
                decoded_into (S.certificates_to_der 'pem_bytes) out_bytes r)
{
  A.pts_to_len pem;
  A.pts_to_len out;
  let mut nb = [| 0uy; 27sz |];
  write_cert_begin nb;
  let mut ne = [| 0uy; 25sz |];
  write_cert_end ne;
  let mut cursor = 0sz;
  let mut der_len = 0sz;
  let mut found = false;
  let mut running = true;
  let mut result : option SZ.t = None #SZ.t;
  assert (pure (Seq.equal (Seq.slice 'out_bytes 0 0) Seq.empty));
  while (!running)
  invariant exists* (vc vd:SZ.t) (vf vr:bool) (res:option SZ.t) (o:B.bytes).
    pts_to cursor vc ** pts_to der_len vd ** pts_to found vf **
    pts_to running vr ** pts_to result res **
    pts_to pem 'pem_bytes ** pts_to out o **
    pts_to nb S.cert_begin ** pts_to ne S.cert_end **
    pure (SZ.v vc <= SZ.v pem_len /\ SZ.v vd <= SZ.v vc /\
          Seq.length o == SZ.v pem_len /\
          (vr ==> S.certificates_to_der 'pem_bytes ==
                  S.certificates_go 'pem_bytes (SZ.v vc) (Seq.slice o 0 (SZ.v vd)) vf) /\
          (not vr ==> decoded_into (S.certificates_to_der 'pem_bytes) o res))
  decreases (SZ.v pem_len - SZ.v !cursor + (if !running then 1 else 0))
  {
    S.cert_begin_bytes ();
    S.cert_end_bytes ();
    let vc = !cursor;
    let vd = !der_len;
    let b = find_needle pem pem_len vc nb 27sz;
    match b {
      None -> {
        let vf = !found;
        if (pem_len <> 0sz && not vf) {
          result := None #SZ.t;
        } else {
          result := Some vd;
        };
        running := false;
      }
      Some vb -> {
        let body = SZ.add vb 27sz;
        let e = find_needle pem pem_len body ne 25sz;
        match e {
          None -> {
            result := None #SZ.t;
            running := false;
          }
          Some ve -> {
            with o. assert (pts_to out o);
            let d = decode_body_into pem body ve out vd;
            match d {
              None -> {
                result := None #SZ.t;
                running := false;
              }
              Some n -> {
                with o'. assert (pts_to out o');
                assert (pure (Seq.equal (Seq.slice o' 0 (SZ.v vd + SZ.v n))
                                        (Seq.append (Seq.slice o 0 (SZ.v vd))
                                                    (Seq.slice o' (SZ.v vd) (SZ.v vd + SZ.v n)))));
                der_len := SZ.add vd n;
                found := true;
                cursor := SZ.add ve 25sz;
              }
            }
          }
        }
      }
    }
  };
  !result
}
#pop-options

#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"
fn private_key_to_der
  (key:array U8.t)
  (key_len:SZ.t)
  (out:array U8.t)
  requires pts_to key 'key_bytes **
           pts_to out 'out_bytes **
           pure (Seq.length 'key_bytes == SZ.v key_len /\
                 Seq.length 'out_bytes == SZ.v key_len)
  returns r:option SZ.t
  ensures exists* out_bytes.
          pts_to key 'key_bytes **
          pts_to out out_bytes **
          pure (Seq.length out_bytes == SZ.v key_len /\
                decoded_into (S.private_key_to_der 'key_bytes) out_bytes r)
{
  A.pts_to_len key;
  A.pts_to_len out;
  if (key_len = 0sz) {
    None #SZ.t
  } else {
    let first = key.(0sz);
    if (first = 0x30uy) {
      AC.copy_prefix key_len key key_len out key_len;
      with o. assert (pts_to out o);
      assert (pure (Seq.equal (Seq.slice o 0 (SZ.v key_len)) 'key_bytes));
      Some key_len
    } else {
      let mut kb = [| 0uy; 11sz |];
      write_key_begin kb;
      let mut ks = [| 0uy; 16sz |];
      write_key_suffix ks;
      let mut ke = [| 0uy; 9sz |];
      write_key_end ke;
      let mut cursor = 0sz;
      let mut running = true;
      let mut result : option SZ.t = None #SZ.t;
      while (!running)
      invariant exists* (vc:SZ.t) (vr:bool) (res:option SZ.t) (o:B.bytes).
        pts_to cursor vc ** pts_to running vr ** pts_to result res **
        pts_to key 'key_bytes ** pts_to out o **
        pts_to kb S.key_begin ** pts_to ks S.key_suffix ** pts_to ke S.key_end **
        pure (SZ.v vc <= SZ.v key_len /\
              Seq.length o == SZ.v key_len /\
              (vr ==> S.private_key_to_der 'key_bytes ==
                      S.private_key_go 'key_bytes (SZ.v vc)) /\
              (not vr ==> decoded_into (S.private_key_to_der 'key_bytes) o res))
      decreases (SZ.v key_len - SZ.v !cursor + (if !running then 1 else 0))
      {
        S.key_begin_bytes ();
        S.key_suffix_bytes ();
        S.key_end_bytes ();
        let vc = !cursor;
        let b = find_needle key key_len vc kb 11sz;
        match b {
          None -> {
            result := None #SZ.t;
            running := false;
          }
          Some vb -> {
            let lab = SZ.add vb 11sz;
            let eol = find_byte key key_len 10uy lab;
            let stop = (if Some? eol then Some?.v eol else key_len);
            let line_end = strip_cr key lab stop;
            let suffix_ok =
              (if (Some? eol && SZ.gte (SZ.sub line_end lab) 16sz)
               then region_eq key (SZ.sub line_end 16sz) ks 0sz 16sz
               else false);
            if suffix_ok {
              let body = SZ.add (Some?.v eol) 1sz;
              let f = find key key_len body ke 9sz lab (SZ.sub line_end lab);
              match f {
                None -> {
                  result := None #SZ.t;
                  running := false;
                }
                Some vf -> {
                  let d = decode_body_into key body vf out 0sz;
                  with o'. assert (pts_to out o');
                  assert (pure (Seq.equal (Seq.slice o' 0 0) Seq.empty));
                  result := d;
                  running := false;
                }
              }
            } else {
              cursor := lab;
            }
          }
        }
      };
      !result
    }
  }
}
#pop-options
