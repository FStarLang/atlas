module TLS13.Impl.X509.Validate

(** Verified X.509 path validation: [validate] accepts only chains that
    [TLS13.X509.Spec.validate_chain] accepts. Certificates are parsed by the
    everparse-asn1 parser generated from [src/asn1/X509.asn] and checked by
    [TLS13.Impl.X509.Check]. *)

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
open TLS13.Impl.X509.Fields

module A = Pulse.Lib.Array
module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CL = TLS13.ConnectionLog
module Ck = TLS13.Impl.X509.Check
module IM = TLS13.Impl.Messages
module L = FStar.List.Tot
module PK = TLS13.Impl.X509.PublicKey
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
module X = TLS13.X509.Chain
module XD = TLS13.X509.Spec.Def
module XP = TLS13.X509.Profile
module XS = TLS13.X509.Spec

inline_for_extraction noextract unfold let ( +^ ) = SZ.add
inline_for_extraction noextract unfold let ( -^ ) = SZ.sub

(** Copied ranges *)

let slice_cb (b:B.bytes) (len:SZ.t) (s e:nat)
  : Lemma (requires s <= e /\ e <= SZ.v len /\ SZ.v len <= B.length b)
          (ensures Seq.slice (cb b len) s e == CL.raw_slice b s e)
  = Seq.lemma_eq_intro (Seq.slice (cb b len) s e) (CL.raw_slice b s e)

let copied_cb (d s:B.bytes) (lo n:nat) (dlen:SZ.t)
  : Lemma (requires CL.raw_slice d 0 n == CL.raw_slice s lo (lo + n) /\
                    lo + n <= B.length s /\ SZ.v dlen == n /\ n <= B.length d)
          (ensures cb d dlen == Seq.slice s lo (lo + n))
  = ()

let copied_slice (d s:B.bytes) (slen:SZ.t) (lo e:nat) (dlen:SZ.t)
  : Lemma (requires CL.raw_slice d 0 (SZ.v dlen) == CL.raw_slice s lo (lo + SZ.v dlen) /\
                    lo + SZ.v dlen == e /\ e <= SZ.v slen /\ SZ.v slen <= B.length s /\
                    SZ.v dlen <= B.length d)
          (ensures cb d dlen == Seq.slice (cb s slen) lo e)
  = slice_cb s slen lo e

(** {2 Trust anchors} *)

(** The anchor store, unlike a certificate, is not capped at
    [PK.max_certificate_len]: a full system root store is far larger. All
    offsets into it stay below [alen], so they fit in [SZ.t]. *)
let a_ok (b:B.bytes) (len:SZ.t) : prop = SZ.v len <= B.length b

fn anchors_wf
  (a:array U8.t) (alen:SZ.t)
  requires pts_to a 'ab ** pure (a_ok 'ab alen)
  returns r:bool
  ensures pts_to a 'ab ** pure (r == X.anchors_wf (cb 'ab alen) 0)
{
  let mut p = 0sz;
  let mut ok = true;
  while (let vp = !p; SZ.lt vp alen)
  invariant exists* (vp:SZ.t) (vok:bool).
    pts_to p vp ** pts_to ok vok ** pts_to a 'ab **
    pure (SZ.v vp <= SZ.v alen /\
          X.anchors_wf (cb 'ab alen) 0 == (vok && X.anchors_wf (cb 'ab alen) (SZ.v vp)))
  decreases (SZ.v alen - SZ.v (!p))
  {
    let vp = !p;
    let d = PK.der_tlv_impl a alen 0x30uy vp alen;
    if (d.ok) {
      p := d.hi;
    } else {
      ok := false;
      p := alen;
    }
  };
  !ok
}

#push-options "--z3rlimit 60"
fn is_anchor
  (c:array U8.t) (len:SZ.t)
  (a:array U8.t) (alen:SZ.t)
  requires pts_to c 'b ** pts_to a 'ab ** pure (ok_len 'b len /\ a_ok 'ab alen)
  returns r:bool
  ensures pts_to c 'b ** pts_to a 'ab **
          pure (r ==> X.is_anchor (cb 'b len) (cb 'ab alen) 0)
{
  let mut p = 0sz;
  let mut found = false;
  while (let vp = !p; SZ.lt vp alen)
  invariant exists* (vp:SZ.t) (vfound:bool).
    pts_to p vp ** pts_to found vfound ** pts_to c 'b ** pts_to a 'ab **
    pure (SZ.v vp <= SZ.v alen /\
          (vfound ==> X.is_anchor (cb 'b len) (cb 'ab alen) 0) /\
          (X.is_anchor (cb 'b len) (cb 'ab alen) (SZ.v vp) ==>
           X.is_anchor (cb 'b len) (cb 'ab alen) 0))
  decreases (SZ.v alen - SZ.v (!p))
  {
    let vp = !p;
    let d = PK.der_tlv_impl a alen 0x30uy vp alen;
    if (d.ok) {
      let eq = range_eq2 c len 0sz len a alen vp d.hi;
      if (eq) {
        found := true;
        p := alen;
      } else {
        p := d.hi;
      }
    } else {
      p := alen;
    }
  };
  !found
}
#pop-options

(** [X.anchored] of the certificate [o], if it parses. *)
let anchored_opt (a:B.bytes) (pos:nat) (o:option XP.certificate) : GTot bool =
  match o with
  | Some v -> X.anchored a pos v
  | None -> false

let anchored_step (a:B.bytes) (pos:nat) (o:option XP.certificate) (e:nat) (anc:B.bytes)
  : Lemma (requires pos < B.length a /\
                    (match C.der_tlv a 0x30uy pos (B.length a) with
                     | Some (_, e') -> e' == e
                     | None -> False) /\
                    anc == Seq.slice a pos e)
          (ensures ((match o with Some v -> X.anchor_issues anc v | None -> false) ==>
                    anchored_opt a pos o) /\
                   (anchored_opt a e o ==> anchored_opt a pos o))
  = ()

let anchor_issues_intro (anc:B.bytes) (o:option XP.certificate) (d:B.bytes) (n:SZ.t)
  : Lemma (requires Ck.names_spec o (Ck.cert_at d n) /\ Ck.signed_spec o (cb d n) /\ cb d n == anc)
          (ensures (match o with Some v -> X.anchor_issues anc v | None -> false))
  = ()

let tlv_bounds (r:PK.der_range) (c:B.bytes) (tag:U8.t) (pos limit:nat)
  : Lemma (requires PK.der_tlv_matches r c tag pos limit /\ r.PK.ok)
          (ensures pos + 2 <= SZ.v r.PK.lo /\ SZ.v r.PK.lo <= SZ.v r.PK.hi /\
                   SZ.v r.PK.hi <= limit /\ limit <= B.length c /\
                   (match C.der_tlv c tag pos limit with
                    | Some (_, e') -> e' == SZ.v r.PK.hi
                    | None -> False))
  = ()

let sz_sub_add (a b:SZ.t)
  : Lemma (requires SZ.v a <= SZ.v b) (ensures SZ.v a + SZ.v (SZ.sub b a) == SZ.v b)
  = ()

#push-options "--z3rlimit 100"
fn anchored
  (a:array U8.t) (alen:SZ.t)
  (c:array U8.t) (len:SZ.t)
  requires pts_to a 'ab ** pts_to c 'b **
           pure (a_ok 'ab alen /\ ok_len 'b len)
  returns ok:bool
  ensures pts_to a 'ab ** pts_to c 'b **
          pure (ok ==> anchored_opt (cb 'ab alen) 0 (Ck.cert_at 'b len))
{
  A.pts_to_len a;
  let av = V.alloc 0uy PK.max_certificate_len;
  V.to_array_pts_to av;
  let mut p = 0sz;
  let mut found = false;
  while (let vp = !p; SZ.lt vp alen)
  invariant exists* (vp:SZ.t) (vfound:bool) (d:B.bytes).
    pts_to p vp ** pts_to found vfound ** pts_to a 'ab ** pts_to c 'b **
    pts_to (V.vec_to_array av) d **
    pure (SZ.v vp <= SZ.v alen /\ B.length d == SZ.v PK.max_certificate_len /\
          (vfound ==> anchored_opt (cb 'ab alen) 0 (Ck.cert_at 'b len)) /\
          (anchored_opt (cb 'ab alen) (SZ.v vp) (Ck.cert_at 'b len) ==>
           anchored_opt (cb 'ab alen) 0 (Ck.cert_at 'b len)))
  decreases (SZ.v alen - SZ.v (!p))
  {
    let vp = !p;
    let t = PK.der_tlv_impl a alen 0x30uy vp alen;
    if (t.ok) {
      tlv_bounds t (cb 'ab alen) 0x30uy (SZ.v vp) (SZ.v alen);
      let n = t.hi -^ vp;
      sz_sub_add vp t.hi;
      if (SZ.gt n PK.max_certificate_len) {
        anchored_step (cb 'ab alen) (SZ.v vp) (Ck.cert_at 'b len) (SZ.v t.hi)
          (Seq.slice (cb 'ab alen) (SZ.v vp) (SZ.v t.hi));
        p := t.hi;
      } else {
        PK.copy_range a vp n (V.vec_to_array av) PK.max_certificate_len;
        with d. assert (pts_to (V.vec_to_array av) d);
        copied_slice d 'ab alen (SZ.v vp) (SZ.v t.hi) n;
        anchored_step (cb 'ab alen) (SZ.v vp) (Ck.cert_at 'b len) (SZ.v t.hi) (cb d n);
        let nm = Ck.names_check c len (V.vec_to_array av) n;
        if (nm) {
          let sg = Ck.signed_check c len (V.vec_to_array av) n;
          if (sg) {
            anchor_issues_intro (cb d n) (Ck.cert_at 'b len) d n;
            found := true;
            p := alen;
          } else {
            p := t.hi;
          }
        } else {
          p := t.hi;
        }
      }
    } else {
      p := alen;
    }
  };
  V.to_vec_pts_to av;
  V.free av;
  !found
}
#pop-options

(** {2 Chains} *)

let rec skip (#a:Type) (n:nat) (l:list a) : list a =
  if n = 0 then l else match l with [] -> [] | _ :: t -> skip (n - 1) t

let rec skip_cons (#a:Type) (k:nat) (l:list a)
  : Lemma (requires k < L.length l)
          (ensures skip k l == L.index l k :: skip (k + 1) l)
          (decreases k)
  = if k = 0 then () else skip_cons (k - 1) (L.tl l)

let rec chain_length (sb:B.bytes) (sl:nat) (ofs ls:Seq.seq SZ.t) (count:nat) (chain:list B.bytes)
  : Lemma (requires IM.certificate_chain_matches sb sl ofs ls count chain)
          (ensures L.length chain == count /\
                   (count > 0 ==> count <= Seq.length ofs /\ count <= Seq.length ls /\
                                  sl <= B.length sb))
          (decreases count)
  = if count = 0 then ()
    else chain_length sb sl (Seq.slice ofs 1 (Seq.length ofs)) (Seq.slice ls 1 (Seq.length ls))
           (count - 1) (L.tl chain)

let rec chain_index (sb:B.bytes) (sl:nat) (ofs ls:Seq.seq SZ.t) (count:nat) (chain:list B.bytes)
  (i:nat)
  : Lemma (requires IM.certificate_chain_matches sb sl ofs ls count chain /\ i < count)
          (ensures i < Seq.length ofs /\ i < Seq.length ls /\ i < L.length chain /\
                   SZ.v (Seq.index ofs i) + SZ.v (Seq.index ls i) <= sl /\
                   sl <= B.length sb /\
                   L.index chain i ==
                     Seq.slice sb (SZ.v (Seq.index ofs i))
                       (SZ.v (Seq.index ofs i) + SZ.v (Seq.index ls i)))
          (decreases count)
  = chain_length sb sl ofs ls count chain;
    let cert :: rest = chain in
    if i = 0 then
      Seq.lemma_eq_elim cert
        (Seq.slice sb (SZ.v (Seq.index ofs 0)) (SZ.v (Seq.index ofs 0) + SZ.v (Seq.index ls 0)))
    else
      chain_index sb sl (Seq.slice ofs 1 (Seq.length ofs)) (Seq.slice ls 1 (Seq.length ls))
        (count - 1) rest (i - 1)

(** [X.chains] of the certificate [c], if it parses. *)
let chains_opt (a:B.bytes) (t:nat) (c:B.bytes) (depth:nat) (rest:list B.bytes) : GTot bool =
  match X.parse_certificate c with
  | Some v -> X.chains a t v depth rest
  | None -> false

let chains_anchored (a:B.bytes) (t:nat) (d:B.bytes) (l:SZ.t) (depth:nat) (rest:list B.bytes)
  : Lemma (requires anchored_opt a 0 (Ck.cert_at d l))
          (ensures chains_opt a t (cb d l) depth rest)
  = ()

let chains_step (a:B.bytes) (t:nat) (dc:B.bytes) (l:SZ.t) (depth:nat) (dn:B.bytes) (l2:SZ.t)
  (rest:list B.bytes) (hb:B.bytes)
  : Lemma (requires Ck.cert_ok_spec (Ck.cert_at dn l2) t false hb true depth /\
                    Ck.names_spec (Ck.cert_at dc l) (Ck.cert_at dn l2) /\
                    Ck.signed_spec (Ck.cert_at dc l) (cb dn l2))
          (ensures chains_opt a t (cb dn l2) (depth + 1) rest ==>
                   chains_opt a t (cb dc l) depth (cb dn l2 :: rest))
  = ()

let below_eq (vk:SZ.t)
  : Lemma (requires SZ.v vk < 0xFFFF) (ensures U32.v (SZ.sizet_to_uint32 vk) == SZ.v vk)
  = assert_norm (pow2 32 == 0x100000000);
    FStar.Math.Lemmas.small_mod (SZ.v vk) (pow2 32)

let chain_ok (sb:B.bytes) (sl:nat) (ofs ls:Seq.seq SZ.t) (count:nat) (chain:list B.bytes) : prop =
  IM.certificate_chain_matches sb sl ofs ls count chain /\
  0 < count /\ sl <= SZ.v PK.max_certificate_len

let goal (a:B.bytes) (t:nat) (chain:list B.bytes{Cons? chain}) : GTot bool =
  chains_opt a t (L.hd chain) 0 (L.tl chain)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
fn chains_from_leaf
  (st:array U8.t) (st_len:SZ.t) (offsets lens:array SZ.t) (count:SZ.t)
  (a:array U8.t) (alen:SZ.t) (h:array U8.t) (hlen:SZ.t) (t:U64.t)
  (#chain:erased (list B.bytes))
  requires pts_to st 'sb ** pts_to offsets 'ofs ** pts_to lens 'ls ** pts_to a 'ab ** pts_to h 'hb **
           pure (chain_ok 'sb (SZ.v st_len) 'ofs 'ls (SZ.v count) chain /\ a_ok 'ab alen /\ ok_len 'hb hlen)
  returns ok:bool
  ensures pts_to st 'sb ** pts_to offsets 'ofs ** pts_to lens 'ls ** pts_to a 'ab ** pts_to h 'hb **
          pure (Cons? chain /\ (ok ==> goal (cb 'ab alen) (U64.v t) chain))
{
  chain_length 'sb (SZ.v st_len) 'ofs 'ls (SZ.v count) chain;
  skip_cons 0 chain;
  let cv = V.alloc 0uy PK.max_certificate_len;
  let nv = V.alloc 0uy PK.max_certificate_len;
  V.to_array_pts_to cv;
  V.to_array_pts_to nv;
  let mut k = 0sz;
  let mut succ = false;
  while (let vk = !k; SZ.lt vk count)
  invariant exists* (vk:SZ.t) (vsucc:bool) (dc dn:B.bytes).
    pts_to k vk ** pts_to succ vsucc **
    pts_to (V.vec_to_array cv) dc ** pts_to (V.vec_to_array nv) dn **
    pts_to st 'sb ** pts_to offsets 'ofs ** pts_to lens 'ls ** pts_to a 'ab ** pts_to h 'hb **
    pure (SZ.v vk <= SZ.v count /\
          B.length dc == SZ.v PK.max_certificate_len /\
          B.length dn == SZ.v PK.max_certificate_len /\
          (vsucc ==> goal (cb 'ab alen) (U64.v t) chain) /\
          (SZ.v vk < SZ.v count ==>
            chains_opt (cb 'ab alen) (U64.v t) (L.index chain (SZ.v vk)) (SZ.v vk)
              (skip (SZ.v vk + 1) chain) ==>
            goal (cb 'ab alen) (U64.v t) chain))
  decreases (SZ.v count - SZ.v (!k))
  {
    let vk = !k;
    chain_index 'sb (SZ.v st_len) 'ofs 'ls (SZ.v count) chain (SZ.v vk);
    let o = offsets.(vk);
    let l = lens.(vk);
    PK.copy_range st o l (V.vec_to_array cv) PK.max_certificate_len;
    with dc. assert (pts_to (V.vec_to_array cv) dc);
    copied_cb dc 'sb (SZ.v o) (SZ.v l) l;
    let an = anchored a alen (V.vec_to_array cv) l;
    if (an) {
      chains_anchored (cb 'ab alen) (U64.v t) dc l (SZ.v vk) (skip (SZ.v vk + 1) chain);
      succ := true;
      k := count;
    } else if (SZ.lt (vk +^ 1sz) count && SZ.lt vk 0xFFFFsz) {
      chain_index 'sb (SZ.v st_len) 'ofs 'ls (SZ.v count) chain (SZ.v vk + 1);
      skip_cons (SZ.v vk + 1) chain;
      let o2 = offsets.(vk +^ 1sz);
      let l2 = lens.(vk +^ 1sz);
      PK.copy_range st o2 l2 (V.vec_to_array nv) PK.max_certificate_len;
      with dn. assert (pts_to (V.vec_to_array nv) dn);
      copied_cb dn 'sb (SZ.v o2) (SZ.v l2) l2;
      let below = SZ.sizet_to_uint32 vk;
      below_eq vk;
      let p = Ck.cert_check (V.vec_to_array nv) l2 t false h hlen true below;
      let nm = Ck.names_check (V.vec_to_array cv) l (V.vec_to_array nv) l2;
      let sg = Ck.signed_check (V.vec_to_array cv) l (V.vec_to_array nv) l2;
      if (p && nm && sg) {
        chains_step (cb 'ab alen) (U64.v t) dc l (SZ.v vk) dn l2
          (skip (SZ.v vk + 2) chain) (cb 'hb hlen);
        k := vk +^ 1sz;
      } else {
        k := count;
      }
    } else {
      k := count;
    }
  };
  V.to_vec_pts_to cv;
  V.to_vec_pts_to nv;
  V.free cv;
  V.free nv;
  !succ
}
#pop-options

(** {2 Validation} *)

let accepted (hostname:B.bytes) (t:nat) (anchors:B.bytes) (chain:list B.bytes) : prop =
  Cons? chain /\
  XS.validate_chain hostname ({ XS.seconds_since_epoch = t }) ({ XS.anchors = anchors }) chain ==
  Some ({ XS.validated_hostname = hostname;
          XS.leaf_public_key = L.hd chain;
          XS.permitted_signature_schemes = [] })

let validate_chain_intro (hostname:B.bytes) (t:nat) (a:B.bytes) (chain:list B.bytes)
  (d:B.bytes) (l:SZ.t)
  : Lemma (requires Cons? chain /\ X.anchors_wf a 0 /\ cb d l == L.hd chain /\
                    Ck.cert_ok_spec (Ck.cert_at d l) t true hostname false 0 /\
                    (X.is_anchor (L.hd chain) a 0 || goal a t chain))
          (ensures accepted hostname t a chain)
  = XD.validate_chain_def hostname ({ XS.seconds_since_epoch = t }) ({ XS.anchors = a }) chain

#push-options "--z3rlimit 120"
fn validate
  (st:array U8.t) (st_len:SZ.t) (offsets lens:array SZ.t) (count:SZ.t)
  (a:array U8.t) (alen:SZ.t)
  (h:array U8.t) (hlen:SZ.t)
  (t:U64.t)
  (#chain:erased (list B.bytes))
  requires pts_to st 'sb ** pts_to offsets 'ofs ** pts_to lens 'ls ** pts_to a 'ab **
           pts_to h 'hb **
           pure (IM.certificate_chain_matches 'sb (SZ.v st_len) 'ofs 'ls (SZ.v count) chain /\
                 SZ.v st_len <= SZ.v PK.max_certificate_len /\
                 a_ok 'ab alen /\ ok_len 'hb hlen)
  returns ok:bool
  ensures pts_to st 'sb ** pts_to offsets 'ofs ** pts_to lens 'ls ** pts_to a 'ab **
          pts_to h 'hb **
          pure (ok ==> accepted (cb 'hb hlen) (U64.v t) (cb 'ab alen) chain)
{
  if (count = 0sz) {
    false
  } else {
    let aw = anchors_wf a alen;
    if (not aw) {
      false
    } else {
      chain_length 'sb (SZ.v st_len) 'ofs 'ls (SZ.v count) chain;
      chain_index 'sb (SZ.v st_len) 'ofs 'ls (SZ.v count) chain 0;
      let lv = V.alloc 0uy PK.max_certificate_len;
      V.to_array_pts_to lv;
      let o = offsets.(0sz);
      let l = lens.(0sz);
      PK.copy_range st o l (V.vec_to_array lv) PK.max_certificate_len;
      with d. assert (pts_to (V.vec_to_array lv) d);
      copied_cb d 'sb (SZ.v o) (SZ.v l) l;
      let pl = Ck.cert_check (V.vec_to_array lv) l t true h hlen false 0ul;
      let ok =
        if (pl) {
          let ia = is_anchor (V.vec_to_array lv) l a alen;
          if (ia) {
            validate_chain_intro (cb 'hb hlen) (U64.v t) (cb 'ab alen) chain d l;
            true
          } else {
            let ch = chains_from_leaf st st_len offsets lens count a alen h hlen t #chain;
            if (ch) {
              validate_chain_intro (cb 'hb hlen) (U64.v t) (cb 'ab alen) chain d l;
              true
            } else {
              false
            }
          }
        } else {
          false
        };
      V.to_vec_pts_to lv;
      V.free lv;
      ok
    }
  }
}
#pop-options

(** Copy the chain's leaf -- the validated peer's [leaf_public_key] -- into
    [out], which must be exactly its length. *)
fn copy_leaf
  (st:array U8.t) (st_len:SZ.t) (offsets lens:array SZ.t) (count:SZ.t)
  (out:array U8.t) (out_len:SZ.t)
  (#chain:erased (list B.bytes))
  requires pts_to st 'sb ** pts_to offsets 'ofs ** pts_to lens 'ls ** pts_to out 'old **
           pure (IM.certificate_chain_matches 'sb (SZ.v st_len) 'ofs 'ls (SZ.v count) chain /\
                 SZ.v st_len <= SZ.v PK.max_certificate_len /\
                 B.length 'old == SZ.v out_len)
  returns ok:bool
  ensures exists* ob.
          pts_to st 'sb ** pts_to offsets 'ofs ** pts_to lens 'ls ** pts_to out ob **
          pure (B.length ob == SZ.v out_len /\ (ok ==> Cons? chain /\ ob == L.hd chain))
{
  if (count = 0sz) {
    false
  } else {
    chain_length 'sb (SZ.v st_len) 'ofs 'ls (SZ.v count) chain;
    chain_index 'sb (SZ.v st_len) 'ofs 'ls (SZ.v count) chain 0;
    let o = offsets.(0sz);
    let l = lens.(0sz);
    if (l = out_len) {
      PK.copy_range st o l out out_len;
      with ob. assert (pts_to out ob);
      assert (pure (Seq.equal ob (L.hd chain)));
      true
    } else {
      false
    }
  }
}

let size_to_u64_fits (x:SZ.t)
  : Lemma (SZ.fits (SZ.v x % pow2 64))
  = SZ.fits_lte (SZ.v x % pow2 64) (SZ.v x)

(** [validate], then [copy_leaf]: on success [out] holds the accepted leaf.
    Rejects anchors too large to scan and times not representable in 64
    bits. *)
fn validate_into
  (st:array U8.t) (st_len:SZ.t) (offsets lens:array SZ.t) (count:SZ.t)
  (a:array U8.t) (alen:SZ.t)
  (h:array U8.t) (hlen:SZ.t)
  (t:SZ.t)
  (out:array U8.t) (out_len:SZ.t)
  (#chain:erased (list B.bytes))
  requires pts_to st 'sb ** pts_to offsets 'ofs ** pts_to lens 'ls ** pts_to a 'ab **
           pts_to h 'hb ** pts_to out 'old **
           pure (IM.certificate_chain_matches 'sb (SZ.v st_len) 'ofs 'ls (SZ.v count) chain /\
                 SZ.v st_len <= SZ.v PK.max_certificate_len /\
                 SZ.v alen <= B.length 'ab /\ ok_len 'hb hlen /\
                 B.length 'old == SZ.v out_len)
  returns ok:bool
  ensures exists* ob.
          pts_to st 'sb ** pts_to offsets 'ofs ** pts_to lens 'ls ** pts_to a 'ab **
          pts_to h 'hb ** pts_to out ob **
          pure (B.length ob == SZ.v out_len /\
                (ok ==> Cons? chain /\ ob == L.hd chain /\
                        accepted (cb 'hb hlen) (SZ.v t) (cb 'ab alen) chain))
{
  let t64 = SZ.sizet_to_uint64 t;
  size_to_u64_fits t;
  if (SZ.uint64_to_sizet t64 = t) {
    let valid = validate st st_len offsets lens count a alen h hlen t64 #chain;
    if valid {
      copy_leaf st st_len offsets lens count out out_len #chain
    } else {
      false
    }
  } else {
    false
  }
}
