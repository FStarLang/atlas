module TLS13.Impl.X509.Validate

(** Verified X.509 path validation: [validate] accepts only chains that
    [TLS13.X509.Spec.validate_chain] accepts. *)

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
open TLS13.Impl.X509.Fields
open TLS13.Impl.X509.Cert

module A = Pulse.Lib.Array
module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CL = TLS13.ConnectionLog
module Cr = TLS13.Crypto
module IM = TLS13.Impl.Messages
module L = FStar.List.Tot
module PK = TLS13.Impl.X509.PublicKey
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
module X = TLS13.X509.Spec

inline_for_extraction noextract unfold let ( +^ ) = SZ.add
inline_for_extraction noextract unfold let ( -^ ) = SZ.sub

(** Copied ranges *)

let slice_cb (b:B.bytes) (len:SZ.t) (s e:nat)
  : Lemma (requires s <= e /\ e <= SZ.v len /\ SZ.v len <= B.length b)
          (ensures X.sub (cb b len) s e == CL.raw_slice b s e /\
                   Seq.slice (cb b len) s e == CL.raw_slice b s e)
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

(** {2 Signatures} *)

fn sha_with_rsa
  (c:array U8.t) (len:SZ.t) (s e:SZ.t) (last:U8.t)
  requires pts_to c 'b ** pure (ok_len 'b len /\ SZ.v s <= SZ.v e /\ SZ.v e <= SZ.v len)
  returns r:bool
  ensures pts_to c 'b ** pure (r == X.sha_with_rsa (cb 'b len) (SZ.v s) (SZ.v e) last)
{
  if (e -^ s = 13sz) {
    let b0 = byte_is c len s 0x06uy;
    let b1 = byte_is c len (s +^ 1sz) 0x09uy;
    let b2 = byte_is c len (s +^ 2sz) 0x2Auy;
    let b3 = byte_is c len (s +^ 3sz) 0x86uy;
    let b4 = byte_is c len (s +^ 4sz) 0x48uy;
    let b5 = byte_is c len (s +^ 5sz) 0x86uy;
    let b6 = byte_is c len (s +^ 6sz) 0xF7uy;
    let b7 = byte_is c len (s +^ 7sz) 0x0Duy;
    let b8 = byte_is c len (s +^ 8sz) 0x01uy;
    let b9 = byte_is c len (s +^ 9sz) 0x01uy;
    let b10 = byte_is c len (s +^ 10sz) last;
    let b11 = byte_is c len (s +^ 11sz) 0x05uy;
    let b12 = byte_is c len (s +^ 12sz) 0x00uy;
    (b0 && b1 && b2 && b3 && b4 && b5 && b6 && b7 && b8 && b9 && b10 && b11 && b12)
  } else {
    false
  }
}

fn ecdsa_with_sha256
  (c:array U8.t) (len:SZ.t) (s e:SZ.t)
  requires pts_to c 'b ** pure (ok_len 'b len /\ SZ.v s <= SZ.v e /\ SZ.v e <= SZ.v len)
  returns r:bool
  ensures pts_to c 'b ** pure (r == X.ecdsa_with_sha256 (cb 'b len) (SZ.v s) (SZ.v e))
{
  if (e -^ s = 10sz) {
    let b0 = byte_is c len s 0x06uy;
    let b1 = byte_is c len (s +^ 1sz) 0x08uy;
    let b2 = byte_is c len (s +^ 2sz) 0x2Auy;
    let b3 = byte_is c len (s +^ 3sz) 0x86uy;
    let b4 = byte_is c len (s +^ 4sz) 0x48uy;
    let b5 = byte_is c len (s +^ 5sz) 0xCEuy;
    let b6 = byte_is c len (s +^ 6sz) 0x3Duy;
    let b7 = byte_is c len (s +^ 7sz) 0x04uy;
    let b8 = byte_is c len (s +^ 8sz) 0x03uy;
    let b9 = byte_is c len (s +^ 9sz) 0x02uy;
    (b0 && b1 && b2 && b3 && b4 && b5 && b6 && b7 && b8 && b9)
  } else {
    false
  }
}

inline_for_extraction noextract
let key_cap : SZ.t = 1024sz

(** What [signed_by] needs to conclude from the key and the verifier. *)
let signed_by_rsa (child:B.bytes) (pc:X.parsed_certificate) (issuer n e:B.bytes)
  (h:C.pkcs1_hash) (last:U8.t)
  : Lemma (requires C.certificate_raw_public_key issuer == Some (C.RawRsa n e) /\
                    X.sha_with_rsa child pc.X.sig_alg_s pc.X.sig_alg_e last /\
                    ((last == 0x0Buy /\ h == C.Pkcs1Sha256) \/
                     (last == 0x0Cuy /\ h == C.Pkcs1Sha384 /\
                      not (X.sha_with_rsa child pc.X.sig_alg_s pc.X.sig_alg_e 0x0Buy)) \/
                     (last == 0x0Duy /\ h == C.Pkcs1Sha512 /\
                      not (X.sha_with_rsa child pc.X.sig_alg_s pc.X.sig_alg_e 0x0Buy) /\
                      not (X.sha_with_rsa child pc.X.sig_alg_s pc.X.sig_alg_e 0x0Cuy))) /\
                    C.rsa_pkcs1_verify h n e (X.sub child pc.X.tbs_s pc.X.tbs_e)
                      (X.sub child pc.X.sig_s pc.X.sig_e))
          (ensures X.signed_by child pc issuer)
  = ()

let signed_by_p256 (child:B.bytes) (pc:X.parsed_certificate) (issuer q:B.bytes)
  : Lemma (requires C.certificate_raw_public_key issuer == Some (C.RawP256 q) /\
                    X.ecdsa_with_sha256 child pc.X.sig_alg_s pc.X.sig_alg_e /\
                    C.ecdsa_secp256r1_sha256_verify q (X.sub child pc.X.tbs_s pc.X.tbs_e)
                      (X.sub child pc.X.sig_s pc.X.sig_e))
          (ensures X.signed_by child pc issuer)
  = ()

#push-options "--z3rlimit 120"
fn signed_by
  (child:array U8.t) (clen:SZ.t) (r:pcert)
  (issuer:array U8.t) (ilen:SZ.t)
  requires pts_to child 'b ** pts_to issuer 'ib **
           pure (ok_len 'b clen /\ pc_ok r (cb 'b clen) /\ ok_len 'ib ilen)
  returns ok:bool
  ensures pts_to child 'b ** pts_to issuer 'ib **
          pure (ok ==> X.signed_by (cb 'b clen) (to_pc r) (cb 'ib ilen))
{
  A.pts_to_len child;
  let tbs_n = r.tbs_e -^ r.tbs_s;
  let sig_n = r.sig_e -^ r.sig_s;
  slice_cb 'b clen (SZ.v r.tbs_s) (SZ.v r.tbs_e);
  slice_cb 'b clen (SZ.v r.sig_s) (SZ.v r.sig_e);
  let tv = V.alloc 0uy PK.max_certificate_len;
  let sv = V.alloc 0uy PK.max_certificate_len;
  let kv = V.alloc 0uy key_cap;
  let ev = V.alloc 0uy key_cap;
  let lv = V.alloc 0sz 2sz;
  V.to_array_pts_to tv;
  V.to_array_pts_to sv;
  V.to_array_pts_to kv;
  V.to_array_pts_to ev;
  V.to_array_pts_to lv;
  PK.copy_range child r.tbs_s tbs_n (V.vec_to_array tv) PK.max_certificate_len;
  PK.copy_range child r.sig_s sig_n (V.vec_to_array sv) PK.max_certificate_len;
  with tb. assert (pts_to (V.vec_to_array tv) tb);
  with sb. assert (pts_to (V.vec_to_array sv) sb);
  let kind =
    PK.certificate_raw_public_key issuer ilen
      (V.vec_to_array kv) key_cap (V.vec_to_array ev) key_cap (V.vec_to_array lv);
  with kb eb ls.
    assert (pts_to (V.vec_to_array kv) kb ** pts_to (V.vec_to_array ev) eb **
            pts_to (V.vec_to_array lv) ls);
  let kl = (V.vec_to_array lv).(0sz);
  let el = (V.vec_to_array lv).(1sz);
  let ok =
    if (kind = 1uy) {
      let a11 = sha_with_rsa child clen r.sig_alg_s r.sig_alg_e 0x0Buy;
      let a12 = sha_with_rsa child clen r.sig_alg_s r.sig_alg_e 0x0Cuy;
      let a13 = sha_with_rsa child clen r.sig_alg_s r.sig_alg_e 0x0Duy;
      if (a11 || a12 || a13) {
        let h = (if a11 then C.Pkcs1Sha256 else if a12 then C.Pkcs1Sha384 else C.Pkcs1Sha512);
        let v =
          Cr.verify_rsa_pkcs1 h
            (V.vec_to_array kv) kl (V.vec_to_array ev) el
            (V.vec_to_array tv) tbs_n (V.vec_to_array sv) sig_n;
        if (v) {
          signed_by_rsa (cb 'b clen) (to_pc r) (cb 'ib ilen)
            (CL.raw_slice kb 0 (SZ.v kl)) (CL.raw_slice eb 0 (SZ.v el)) h
            (if a11 then 0x0Buy else if a12 then 0x0Cuy else 0x0Duy);
          true
        } else {
          false
        }
      } else {
        false
      }
    } else if (kind = 2uy) {
      let ec = ecdsa_with_sha256 child clen r.sig_alg_s r.sig_alg_e;
      if (ec) {
        let v =
          Cr.verify_ecdsa_secp256r1_sha256
            (V.vec_to_array kv) kl (V.vec_to_array tv) tbs_n (V.vec_to_array sv) sig_n;
        if (v) {
          signed_by_p256 (cb 'b clen) (to_pc r) (cb 'ib ilen) (CL.raw_slice kb 0 (SZ.v kl));
          true
        } else {
          false
        }
      } else {
        false
      }
    } else {
      false
    };
  V.to_vec_pts_to tv;
  V.to_vec_pts_to sv;
  V.to_vec_pts_to kv;
  V.to_vec_pts_to ev;
  V.to_vec_pts_to lv;
  V.free tv;
  V.free sv;
  V.free kv;
  V.free ev;
  V.free lv;
  ok
}
#pop-options

(** {2 Trust anchors} *)

fn anchors_wf
  (a:array U8.t) (alen:SZ.t)
  requires pts_to a 'ab ** pure (ok_len 'ab alen)
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
  requires pts_to c 'b ** pts_to a 'ab ** pure (ok_len 'b len /\ ok_len 'ab alen)
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

let anchored_step (a:B.bytes) (pos:nat) (child:B.bytes) (pc:X.parsed_certificate)
  (e:nat) (anc:B.bytes)
  : Lemma (requires pos < B.length a /\
                    (match C.der_tlv a 0x30uy pos (B.length a) with
                     | Some (_, e') -> e' == e
                     | None -> False) /\
                    anc == Seq.slice a pos e)
          (ensures (X.anchor_issues anc child pc ==> X.anchored a pos child pc) /\
                   (X.anchored a e child pc ==> X.anchored a pos child pc))
  = ()

let anchor_issues_intro (anc child:B.bytes) (pc:X.parsed_certificate) (pa:X.parsed_certificate)
  : Lemma (requires X.parse_certificate anc == Some pa /\
                    X.range_eq anc pa.X.fields.X.subject_s pa.X.fields.X.subject_e
                      child pc.X.fields.X.issuer_s pc.X.fields.X.issuer_e /\
                    X.signed_by child pc anc)
          (ensures X.anchor_issues anc child pc)
  = ()

let tlv_bounds (r:PK.der_range) (c:B.bytes) (tag:U8.t) (pos limit:nat)
  : Lemma (requires PK.der_tlv_matches r c tag pos limit /\ r.PK.ok)
          (ensures pos + 2 <= SZ.v r.PK.lo /\ SZ.v r.PK.lo <= SZ.v r.PK.hi /\
                   SZ.v r.PK.hi <= limit /\ limit <= B.length c /\
                   (match C.der_tlv c tag pos limit with
                    | Some (_, e') -> e' == SZ.v r.PK.hi
                    | None -> False))
  = ()

#push-options "--z3rlimit 100"
fn anchored
  (a:array U8.t) (alen:SZ.t)
  (c:array U8.t) (len:SZ.t) (r:pcert)
  requires pts_to a 'ab ** pts_to c 'b **
           pure (ok_len 'ab alen /\ ok_len 'b len /\ pc_ok r (cb 'b len))
  returns ok:bool
  ensures pts_to a 'ab ** pts_to c 'b **
          pure (ok ==> X.anchored (cb 'ab alen) 0 (cb 'b len) (to_pc r))
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
          (vfound ==> X.anchored (cb 'ab alen) 0 (cb 'b len) (to_pc r)) /\
          (X.anchored (cb 'ab alen) (SZ.v vp) (cb 'b len) (to_pc r) ==>
           X.anchored (cb 'ab alen) 0 (cb 'b len) (to_pc r)))
  decreases (SZ.v alen - SZ.v (!p))
  {
    let vp = !p;
    let t = PK.der_tlv_impl a alen 0x30uy vp alen;
    if (t.ok) {
      tlv_bounds t (cb 'ab alen) 0x30uy (SZ.v vp) (SZ.v alen);
      let n = t.hi -^ vp;
      assert (pure (SZ.v vp + SZ.v n == SZ.v t.hi));
      PK.copy_range a vp n (V.vec_to_array av) PK.max_certificate_len;
      with d. assert (pts_to (V.vec_to_array av) d);
      copied_slice d 'ab alen (SZ.v vp) (SZ.v t.hi) n;
      anchored_step (cb 'ab alen) (SZ.v vp) (cb 'b len) (to_pc r) (SZ.v t.hi) (cb d n);
      let pa = parse_certificate (V.vec_to_array av) n;
      if (pa.pc_ok) {
        let nm = range_eq2 (V.vec_to_array av) n pa.subject_s pa.subject_e c len r.issuer_s r.issuer_e;
        if (nm) {
          let sg = signed_by c len r (V.vec_to_array av) n;
          if (sg) {
            anchor_issues_intro (cb d n) (cb 'b len) (to_pc r) (to_pc pa);
            found := true;
            p := alen;
          } else {
            p := t.hi;
          }
        } else {
          p := t.hi;
        }
      } else {
        p := t.hi;
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

let chains_anchored (a:B.bytes) (t:nat) (child:B.bytes) (depth:nat) (rest:X.cert_chain)
  (pc:X.parsed_certificate)
  : Lemma (requires X.parse_certificate child == Some pc /\ X.anchored a 0 child pc)
          (ensures X.chains a t child depth rest)
  = ()

let chains_step (a:B.bytes) (t:nat) (child:B.bytes) (depth:nat) (next:B.bytes)
  (rest:X.cert_chain) (pc pn:X.parsed_certificate)
  : Lemma (requires X.parse_certificate child == Some pc /\ X.parse_certificate next == Some pn /\
                    X.path_certificate_ok next pn t /\ X.issuer_ok next pn depth /\
                    X.range_eq child pc.X.fields.X.issuer_s pc.X.fields.X.issuer_e
                      next pn.X.fields.X.subject_s pn.X.fields.X.subject_e /\
                    X.signed_by child pc next)
          (ensures X.chains a t next (depth + 1) rest ==> X.chains a t child depth (next :: rest))
  = ()

let chain_ok (sb:B.bytes) (sl:nat) (ofs ls:Seq.seq SZ.t) (count:nat) (chain:list B.bytes) : prop =
  IM.certificate_chain_matches sb sl ofs ls count chain /\
  0 < count /\ sl <= SZ.v PK.max_certificate_len

let goal (a:B.bytes) (t:nat) (chain:list B.bytes{Cons? chain}) : GTot bool =
  X.chains a t (L.hd chain) 0 (L.tl chain)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
fn chains_from_leaf
  (st:array U8.t) (st_len:SZ.t) (offsets lens:array SZ.t) (count:SZ.t)
  (a:array U8.t) (alen:SZ.t) (t:U64.t)
  (#chain:erased (list B.bytes))
  requires pts_to st 'sb ** pts_to offsets 'ofs ** pts_to lens 'ls ** pts_to a 'ab **
           pure (chain_ok 'sb (SZ.v st_len) 'ofs 'ls (SZ.v count) chain /\ ok_len 'ab alen)
  returns ok:bool
  ensures pts_to st 'sb ** pts_to offsets 'ofs ** pts_to lens 'ls ** pts_to a 'ab **
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
    pts_to st 'sb ** pts_to offsets 'ofs ** pts_to lens 'ls ** pts_to a 'ab **
    pure (SZ.v vk <= SZ.v count /\
          B.length dc == SZ.v PK.max_certificate_len /\
          B.length dn == SZ.v PK.max_certificate_len /\
          (vsucc ==> goal (cb 'ab alen) (U64.v t) chain) /\
          (SZ.v vk < SZ.v count ==>
            X.chains (cb 'ab alen) (U64.v t) (L.index chain (SZ.v vk)) (SZ.v vk)
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
    let pc = parse_certificate (V.vec_to_array cv) l;
    if (pc.pc_ok) {
      let an = anchored a alen (V.vec_to_array cv) l pc;
      if (an) {
        chains_anchored (cb 'ab alen) (U64.v t) (cb dc l) (SZ.v vk) (skip (SZ.v vk + 1) chain)
          (to_pc pc);
        succ := true;
        k := count;
      } else if (SZ.lt (vk +^ 1sz) count) {
        chain_index 'sb (SZ.v st_len) 'ofs 'ls (SZ.v count) chain (SZ.v vk + 1);
        skip_cons (SZ.v vk + 1) chain;
        let o2 = offsets.(vk +^ 1sz);
        let l2 = lens.(vk +^ 1sz);
        PK.copy_range st o2 l2 (V.vec_to_array nv) PK.max_certificate_len;
        with dn. assert (pts_to (V.vec_to_array nv) dn);
        copied_cb dn 'sb (SZ.v o2) (SZ.v l2) l2;
        let pn = parse_certificate (V.vec_to_array nv) l2;
        if (pn.pc_ok) {
          let p = path_certificate_ok (V.vec_to_array nv) l2 pn t;
          let io = issuer_ok (V.vec_to_array nv) l2 pn vk;
          let nm =
            range_eq2 (V.vec_to_array cv) l pc.issuer_s pc.issuer_e
              (V.vec_to_array nv) l2 pn.subject_s pn.subject_e;
          let sg = signed_by (V.vec_to_array cv) l pc (V.vec_to_array nv) l2;
          if (p && io && nm && sg) {
            chains_step (cb 'ab alen) (U64.v t) (cb dc l) (SZ.v vk) (cb dn l2)
              (skip (SZ.v vk + 2) chain) (to_pc pc) (to_pc pn);
            k := vk +^ 1sz;
          } else {
            k := count;
          }
        } else {
          k := count;
        }
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
  X.validate_chain hostname ({ X.seconds_since_epoch = t }) ({ X.anchors = anchors }) chain ==
  Some ({ X.validated_hostname = hostname;
          X.leaf_public_key = L.hd chain;
          X.permitted_signature_schemes = [] })

let validate_chain_intro (hostname:B.bytes) (t:nat) (a:B.bytes) (chain:list B.bytes)
  (pl:X.parsed_certificate)
  : Lemma (requires Cons? chain /\ X.anchors_wf a 0 /\
                    X.parse_certificate (L.hd chain) == Some pl /\
                    X.path_certificate_ok (L.hd chain) pl t /\
                    X.leaf_ok (L.hd chain) pl hostname /\
                    (X.is_anchor (L.hd chain) a 0 || X.chains a t (L.hd chain) 0 (L.tl chain)))
          (ensures accepted hostname t a chain)
  = reveal_opaque (`%X.validate_chain)
      (X.validate_chain hostname ({ X.seconds_since_epoch = t }) ({ X.anchors = a }) chain)

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
                 ok_len 'ab alen /\ ok_len 'hb hlen)
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
      let pl = parse_certificate (V.vec_to_array lv) l;
      let ok =
        if (pl.pc_ok) {
          let p = path_certificate_ok (V.vec_to_array lv) l pl t;
          let lf = leaf_ok (V.vec_to_array lv) l pl h hlen;
          if (p && lf) {
            let ia = is_anchor (V.vec_to_array lv) l a alen;
            if (ia) {
              validate_chain_intro (cb 'hb hlen) (U64.v t) (cb 'ab alen) chain (to_pc pl);
              true
            } else {
              let ch = chains_from_leaf st st_len offsets lens count a alen t #chain;
              if (ch) {
                validate_chain_intro (cb 'hb hlen) (U64.v t) (cb 'ab alen) chain (to_pc pl);
                true
              } else {
                false
              }
            }
          } else {
            false
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
  if (SZ.lte alen PK.max_certificate_len && SZ.uint64_to_sizet t64 = t) {
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
