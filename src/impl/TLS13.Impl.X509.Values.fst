module TLS13.Impl.X509.Values

(** The checks of [TLS13.X509.Chain] on extension values, given as the
    bytes [d[0, len)] of an array (copied there by [Exts.find_ext]). Each
    fails closed: [r ==> spec]. *)

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
module Cast = FStar.Int.Cast
module E = ASN1.Spec.Content.Enc
module F = TLS13.Impl.X509.Fields
module N = TLS13.Impl.X509.Names
module PK = TLS13.Impl.X509.PublicKey
module PS = ASN1.Pulse.ParseSeqOf
module I64 = FStar.Int64
module KS = TLS13.X509.KeySpec
module L = FStar.List.Tot
module S = Pulse.Lib.Slice
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module X = TLS13.Wire.Generated.X509
module XP = TLS13.X509.Profile

(** {2 BasicConstraints} *)

let ca_m (c: t_BasicConstraints_cA_opt) (y: asn1_t X.k_BasicConstraints) : slprop =
  match c, fst y with
  | BasicConstraints_cA_absent, Default -> emp
  | BasicConstraints_cA_present a, Nondefault b -> pure (a == b)
  | _ -> pure False

let pl_m (pm: perm) (p: t_BasicConstraints_pathLenConstraint_opt) (y: asn1_t X.k_BasicConstraints) : slprop =
  match p, snd y with
  | BasicConstraints_pathLenConstraint_absent, None -> emp
  | BasicConstraints_pathLenConstraint_present a, Some b -> asn1_int_rel asn1_any_integer_bound pm a b
  | _ -> pure False

let bc_split (pm: perm) (x: t_BasicConstraints) (y: asn1_t X.k_BasicConstraints)
: Lemma (arel true d_BasicConstraints pm x y == (ca_m x.cA y ** pl_m pm x.pathLenConstraint y))
= bc_eq pm x y;
  assert (bc_m pm x y == (ca_m x.cA y ** pl_m pm x.pathLenConstraint y))
    by (FStar.Tactics.norm [delta_only [`%bc_m; `%ca_m; `%pl_m]]; FStar.Tactics.trefl ())

(** What [bc_ok] accepts: cA, and a non-negative pathLen of at least [below]. *)
let bc_accept (x: t_BasicConstraints) (below: U32.t) : bool =
  (match x.cA with
   | BasicConstraints_cA_present a -> a
   | BasicConstraints_cA_absent -> false) &&
  (match x.pathLenConstraint with
   | BasicConstraints_pathLenConstraint_absent -> true
   | BasicConstraints_pathLenConstraint_present (Small i) -> I64.lte (Cast.uint32_to_int64 below) i
   | BasicConstraints_pathLenConstraint_present (Big _) -> false)

#push-options "--ifuel 2 --z3rlimit 40"
ghost fn bc_info (pm: perm) (x: t_BasicConstraints) (y: asn1_t X.k_BasicConstraints) (below: U32.t)
  requires ca_m x.cA y ** pl_m pm x.pathLenConstraint y ** pure (bc_accept x below)
  ensures ca_m x.cA y ** pl_m pm x.pathLenConstraint y **
          pure (v_of_default (fst y) /\ (match snd y with None -> True | Some n -> U32.v below <= n))
{
  if (Default? (fst y)) {
    rewrite (ca_m x.cA y) as pure False;
    unreachable ()
  } else {
    rewrite (ca_m x.cA y) as pure (BasicConstraints_cA_present?.v x.cA == Nondefault?.v' (fst y));
    rewrite (pure (BasicConstraints_cA_present?.v x.cA == Nondefault?.v' (fst y))) as (ca_m x.cA y);
    if (BasicConstraints_pathLenConstraint_absent? x.pathLenConstraint) {
      if (Some? (snd y)) {
        rewrite (pl_m pm x.pathLenConstraint y) as pure False;
        unreachable ()
      } else {
        ()
      }
    } else {
      if (Some? (snd y)) {
        rewrite (pl_m pm x.pathLenConstraint y)
             as (asn1_int_rel asn1_any_integer_bound pm (BasicConstraints_pathLenConstraint_present?.v x.pathLenConstraint) (Some?.v (snd y)));
        rewrite (asn1_int_rel asn1_any_integer_bound pm (BasicConstraints_pathLenConstraint_present?.v x.pathLenConstraint) (Some?.v (snd y)))
             as pure ((I64.v (Small?._0 (BasicConstraints_pathLenConstraint_present?.v x.pathLenConstraint)) <: int) == (Some?.v (snd y) <: int));
        rewrite pure ((I64.v (Small?._0 (BasicConstraints_pathLenConstraint_present?.v x.pathLenConstraint)) <: int) == (Some?.v (snd y) <: int))
             as (asn1_int_rel asn1_any_integer_bound pm (BasicConstraints_pathLenConstraint_present?.v x.pathLenConstraint) (Some?.v (snd y)));
        rewrite (asn1_int_rel asn1_any_integer_bound pm (BasicConstraints_pathLenConstraint_present?.v x.pathLenConstraint) (Some?.v (snd y)))
             as (pl_m pm x.pathLenConstraint y)
      } else {
        rewrite (pl_m pm x.pathLenConstraint y) as pure False;
        unreachable ()
      }
    }
  }
}

#pop-options

(** [C.ca_allows (d[0, len)) below], failing closed. *)
fn bc_ok (buf: A.array U8.t) (#p: perm) (#d: Ghost.erased (Seq.seq U8.t)) (len: SZ.t{SZ.v len <= Seq.length d}) (below: U32.t)
  requires A.pts_to buf #p d ** pure (SZ.v len <= Seq.length d)
  returns r: bool
  ensures A.pts_to buf #p d ** pure (r ==> C.ca_allows (Seq.slice d 0 (SZ.v len)) (U32.v below))
{
  let s = prefix_slice buf #p #d len;
  let o = open_whole validate_BasicConstraints parse_BasicConstraints s;
  match o {
    None -> {
      unfold (whole_res d_BasicConstraints p s (Seq.slice d 0 (SZ.v len)) None);
      elim_trade (S.pts_to s #p (Seq.slice d 0 (SZ.v len))) (A.pts_to buf #p d);
      false
    }
    Some x -> {
      unfold (whole_res d_BasicConstraints p s (Seq.slice d 0 (SZ.v len)) (Some x));
      with v. assert (arel true d_BasicConstraints p x v);
      let ok = bc_accept x below;
      bc_split p x v;
      rewrite (arel true d_BasicConstraints p x v) as (ca_m x.cA v ** pl_m p x.pathLenConstraint v);
      if ok {
        bc_info p x v below;
        ()
      } else {
        ()
      };
      rewrite (ca_m x.cA v ** pl_m p x.pathLenConstraint v) as (arel true d_BasicConstraints p x v);
      elim_trade (arel true d_BasicConstraints p x v) (S.pts_to s #p (Seq.slice d 0 (SZ.v len)));
      elim_trade (S.pts_to s #p (Seq.slice d 0 (SZ.v len))) (A.pts_to buf #p d);
      ok
    }
  }
}

(** {2 KeyUsage} *)

(** [C.key_usage_bits (d[0, len))] allows [mask], failing closed. *)
fn ku_ok (buf: A.array U8.t) (#p: perm) (#d: Ghost.erased (Seq.seq U8.t)) (len: SZ.t{SZ.v len <= Seq.length d}) (mask: U8.t)
  requires A.pts_to buf #p d ** pure (SZ.v len <= Seq.length d)
  returns r: bool
  ensures A.pts_to buf #p d **
          pure (r ==> (match C.key_usage_bits (Seq.slice d 0 (SZ.v len)) with
                       | Some b -> C.has_bit b mask
                       | None -> false))
{
  let s = prefix_slice buf #p #d len;
  let o = open_whole validate_KeyUsage parse_KeyUsage s;
  match o {
    None -> {
      unfold (whole_res d_KeyUsage p s (Seq.slice d 0 (SZ.v len)) None);
      elim_trade (S.pts_to s #p (Seq.slice d 0 (SZ.v len))) (A.pts_to buf #p d);
      false
    }
    Some x -> {
      unfold (whole_res d_KeyUsage p s (Seq.slice d 0 (SZ.v len)) (Some x));
      with v. assert (arel true d_KeyUsage p x v);
      ku_eq p x v;
      rewrite (arel true d_KeyUsage p x v) as (asn1_bitstring_rel p x v);
      unfold (asn1_bitstring_rel p x v);
      let bs = x.bytes;
      with wb. assert (S.pts_to x.bytes #p wb);
      rewrite (S.pts_to x.bytes #p wb) as (S.pts_to bs #p wb);
      S.pts_to_len bs;
      let mut b = 0uy;
      if (SZ.gt (S.len bs) 0sz) {
        let b0 = S.(bs.(0sz));
        b := b0;
      };
      rewrite (S.pts_to bs #p wb) as (S.pts_to x.bytes #p wb);
      fold (asn1_bitstring_rel p x v);
      rewrite (asn1_bitstring_rel p x v) as (arel true d_KeyUsage p x v);
      elim_trade (arel true d_KeyUsage p x v) (S.pts_to s #p (Seq.slice d 0 (SZ.v len)));
      elim_trade (S.pts_to s #p (Seq.slice d 0 (SZ.v len))) (A.pts_to buf #p d);
      let vb = !b;
      C.has_bit vb mask
    }
  }
}

(** {2 ExtKeyUsageSyntax} *)

inline_for_extraction noextract
let eq_server_auth : eq_from_t C.server_auth_oid =
  norm [delta_only [`%mk_eq; `%C.server_auth_oid]; zeta; iota; primops] (mk_eq C.server_auth_oid)
inline_for_extraction noextract
let eq_any_eku : eq_from_t C.any_eku_oid =
  norm [delta_only [`%mk_eq; `%C.any_eku_oid]; zeta; iota; primops] (mk_eq C.any_eku_oid)

fn lit_server_auth (s: S.slice U8.t) (#pm: perm) (#w: Ghost.erased (Seq.seq U8.t))
  requires S.pts_to s #pm w
  returns r: bool
  ensures S.pts_to s #pm w ** pure (r <==> KS.bytes_is w C.server_auth_oid)
{
  S.pts_to_len s;
  let r = eq_server_auth s 0sz #pm #w;
  assert (pure (Seq.slice w 0 (Seq.length w) `Seq.equal` w));
  r
}

fn lit_any_eku (s: S.slice U8.t) (#pm: perm) (#w: Ghost.erased (Seq.seq U8.t))
  requires S.pts_to s #pm w
  returns r: bool
  ensures S.pts_to s #pm w ** pure (r <==> KS.bytes_is w C.any_eku_oid)
{
  S.pts_to_len s;
  let r = eq_any_eku s 0sz #pm #w;
  assert (pure (Seq.slice w 0 (Seq.length w) `Seq.equal` w));
  r
}

(** Whether the KeyPurposeId [x] allows TLS server authentication. *)
fn kp_ok (x: S.slice U8.t) (#q: perm) (#h: Ghost.erased (asn1_t X.k_KeyPurposeId))
  requires arel true d_KeyPurposeId q x h
  returns r: bool
  ensures arel true d_KeyPurposeId q x h **
          pure (r == (KS.bytes_is (C.purpose_bytes h) C.server_auth_oid || KS.bytes_is (C.purpose_bytes h) C.any_eku_oid))
{
  kp_eq q x h;
  rewrite (arel true d_KeyPurposeId q x h) as (oid_rel q x h);
  unfold (oid_rel q x h);
  unfold (prel_slice_ser (E.leaf_enc ASN1_OID) q x h);
  let a = lit_server_auth x;
  let b = lit_any_eku x;
  fold (prel_slice_ser (E.leaf_enc ASN1_OID) q x h);
  fold (oid_rel q x h);
  rewrite (oid_rel q x h) as (arel true d_KeyPurposeId q x h);
  (a || b)
}

#push-options "--z3rlimit 80 --fuel 2 --ifuel 2"
(** [C.eku_server_auth l], failing closed. *)
fn kps_ok (input: S.slice U8.t) (count: SZ.t) (#q: perm) (#w: Ghost.erased (Seq.seq U8.t))
  (#l: Ghost.erased (list (asn1_t X.k_KeyPurposeId)))
  requires S.pts_to input #q w ** pure (nl_at X.k_KeyPurposeId w 0 (SZ.v count) l)
  returns r: bool
  ensures S.pts_to input #q w ** pure (r ==> C.eku_server_auth l)
{
  let mut off = 0sz;
  let mut i = count;
  let mut fin = false;
  nl_rest_eq X.k_KeyPurposeId w 0 (SZ.v count) l;
  while (let vi = !i; let vf = !fin; (not vf && SZ.gt vi 0sz))
  invariant exists* (voff vi: SZ.t) (vf: bool).
    pts_to off voff ** pts_to i vi ** pts_to fin vf ** S.pts_to input #q w **
    pure ((vf ==> C.eku_server_auth l) /\
          (not vf ==> nl_at X.k_KeyPurposeId w (SZ.v voff) (SZ.v vi) (nl_rest X.k_KeyPurposeId w (SZ.v voff) (SZ.v vi)) /\
                      (C.eku_server_auth (nl_rest X.k_KeyPurposeId w (SZ.v voff) (SZ.v vi)) ==> C.eku_server_auth l)))
  decreases ((if !fin then 0 else 1) + SZ.v (!i))
  {
    let vi = !i;
    let voff = !off;
    let p = nl_elem validate_KeyPurposeId parse_KeyPurposeId input voff (SZ.v vi - 1) #q #w
      #(nl_rest X.k_KeyPurposeId w (SZ.v voff) (SZ.v vi));
    let x = fst p;
    with h. assert (arel true d_KeyPurposeId q (fst p) h);
    rewrite each (fst p) as x;
    let hit = kp_ok x;
    elim_trade (arel true d_KeyPurposeId q x h) (S.pts_to input #q w);
    if hit {
      fin := true;
    } else {
      nl_rest_eq X.k_KeyPurposeId w (SZ.v (snd p)) (SZ.v vi - 1) (L.tl (nl_rest X.k_KeyPurposeId w (SZ.v voff) (SZ.v vi)));
      off := snd p;
      i := SZ.sub vi 1sz;
    }
  };
  let vf = !fin;
  vf
}
#pop-options

(** [d[0, len)] is an ExtKeyUsageSyntax allowing server authentication,
    failing closed. *)
fn eku_ok (buf: A.array U8.t) (#p: perm) (#d: Ghost.erased (Seq.seq U8.t)) (len: SZ.t{SZ.v len <= Seq.length d})
  requires A.pts_to buf #p d
  returns r: bool
  ensures A.pts_to buf #p d **
          pure (r ==> (match XP.parse_full X.k_ExtKeyUsageSyntax (Seq.slice d 0 (SZ.v len)) with
                       | Some ks -> C.eku_server_auth ks
                       | None -> false))
{
  let s = prefix_slice buf #p #d len;
  let o = open_whole validate_ExtKeyUsageSyntax parse_ExtKeyUsageSyntax s;
  match o {
    None -> {
      unfold (whole_res d_ExtKeyUsageSyntax p s (Seq.slice d 0 (SZ.v len)) None);
      elim_trade (S.pts_to s #p (Seq.slice d 0 (SZ.v len))) (A.pts_to buf #p d);
      false
    }
    Some x -> {
      unfold (whole_res d_ExtKeyUsageSyntax p s (Seq.slice d 0 (SZ.v len)) (Some x));
      with v. assert (arel true d_ExtKeyUsageSyntax p x v);
      eku_eq p x v;
      let vl : Ghost.erased (list (asn1_t X.k_KeyPurposeId)) = Ghost.elift1 (fun (y: asn1_t X.k_ExtKeyUsageSyntax) -> (y <: list (asn1_t X.k_KeyPurposeId))) v;
      rewrite (arel true d_ExtKeyUsageSyntax p x v) as (PS.ml_match d_KeyPurposeId p x vl);
      let it = ml_open d_KeyPurposeId x #p #vl;
      with q w. assert (S.pts_to (fst it) #q w);
      let ok = kps_ok (fst it) (snd it) #q #w #vl;
      elim_trade (S.pts_to (fst it) #q w) (PS.ml_match d_KeyPurposeId p x vl);
      rewrite (PS.ml_match d_KeyPurposeId p x vl) as (arel true d_ExtKeyUsageSyntax p x v);
      elim_trade (arel true d_ExtKeyUsageSyntax p x v) (S.pts_to s #p (Seq.slice d 0 (SZ.v len)));
      elim_trade (S.pts_to s #p (Seq.slice d 0 (SZ.v len))) (A.pts_to buf #p d);
      ok
    }
  }
}

(** {2 subjectAltName} *)

ghost fn dns_open (q: perm) (s: S.slice U8.t) (hg: asn1_t X.k_GeneralName)
  requires gn_dns_m q s hg
  ensures exists* w. S.pts_to s #q w **
          pure (dfst hg == C.id_dns_name /\ w == E.leaf_enc ASN1_IA5STRING (C.gn_dns_name hg))
{
  if (dfst hg = C.id_dns_name) {
    rewrite (gn_dns_m q s hg) as (prel_slice_ser (E.leaf_enc ASN1_IA5STRING) q s (C.gn_dns_name hg));
    unfold (prel_slice_ser (E.leaf_enc ASN1_IA5STRING) q s (C.gn_dns_name hg))
  } else {
    rewrite (gn_dns_m q s hg) as pure False;
    unreachable ()
  }
}

ghost fn dns_close (q: perm) (s: S.slice U8.t) (hg: asn1_t X.k_GeneralName) (#w: Seq.seq U8.t)
  requires S.pts_to s #q w **
           pure (dfst hg == C.id_dns_name /\ w == E.leaf_enc ASN1_IA5STRING (C.gn_dns_name hg))
  ensures gn_dns_m q s hg
{
  fold (prel_slice_ser (E.leaf_enc ASN1_IA5STRING) q s (C.gn_dns_name hg));
  rewrite (prel_slice_ser (E.leaf_enc ASN1_IA5STRING) q s (C.gn_dns_name hg)) as (gn_dns_m q s hg)
}

ghost fn ip_open (q: perm) (s: S.slice U8.t) (hg: asn1_t X.k_GeneralName)
  requires gn_ip_m q s hg
  ensures exists* w. S.pts_to s #q w **
          pure (dfst hg == C.id_ip_address /\ w == E.leaf_enc ASN1_OCTETSTRING (C.gn_ip_address hg))
{
  if (dfst hg = C.id_ip_address) {
    rewrite (gn_ip_m q s hg) as (prel_slice_ser (E.leaf_enc ASN1_OCTETSTRING) q s (C.gn_ip_address hg));
    unfold (prel_slice_ser (E.leaf_enc ASN1_OCTETSTRING) q s (C.gn_ip_address hg))
  } else {
    rewrite (gn_ip_m q s hg) as pure False;
    unreachable ()
  }
}

ghost fn ip_close (q: perm) (s: S.slice U8.t) (hg: asn1_t X.k_GeneralName) (#w: Seq.seq U8.t)
  requires S.pts_to s #q w **
           pure (dfst hg == C.id_ip_address /\ w == E.leaf_enc ASN1_OCTETSTRING (C.gn_ip_address hg))
  ensures gn_ip_m q s hg
{
  fold (prel_slice_ser (E.leaf_enc ASN1_OCTETSTRING) q s (C.gn_ip_address hg));
  rewrite (prel_slice_ser (E.leaf_enc ASN1_OCTETSTRING) q s (C.gn_ip_address hg)) as (gn_ip_m q s hg)
}

let cb_slice (d: Seq.seq U8.t) (n: SZ.t) (w: Seq.seq U8.t)
: Lemma (requires SZ.v n <= Seq.length d /\ Seq.slice d 0 (SZ.v n) == w)
        (ensures F.cb d n == w)
= assert (Seq.equal (F.cb d n) w)

(** The host: [cb hb hlen] and its IPv4 reading [ip]. *)
let host_ok (hb: Seq.seq U8.t) (hlen: SZ.t) (ip: N.ip_v) : prop =
  F.ok_len hb hlen /\ N.to_ip ip == C.ipv4_address (F.cb hb hlen)

let scratch_ok (dn: Seq.seq U8.t) (nb: A.array U8.t) (nblen: SZ.t) : prop =
  A.length nb == SZ.v nblen /\ SZ.v nblen <= SZ.v PK.max_certificate_len

#push-options "--z3rlimit 80"
(** Whether the GeneralName [g] names the host, copying it into [nb]. *)
fn gn_ok (g: t_GeneralName) (#q: perm) (#hg: Ghost.erased (asn1_t X.k_GeneralName))
  (h: A.array U8.t) (hlen: SZ.t) (#hb: Ghost.erased (Seq.seq U8.t)) (ip: N.ip_v)
  (nb: A.array U8.t) (nblen: SZ.t) (#dn: Ghost.erased (Seq.seq U8.t))
  requires arel true d_GeneralName q g hg ** A.pts_to h hb ** A.pts_to nb dn **
           pure (host_ok hb hlen ip /\ scratch_ok dn nb nblen)
  returns r: bool
  ensures arel true d_GeneralName q g hg ** A.pts_to h hb ** (exists* dn'. A.pts_to nb dn' **
          pure (scratch_ok dn' nb nblen /\ (r ==> C.gn_matches (F.cb hb hlen) (N.to_ip ip) hg)))
{
  match g {
    GeneralName_dNSName s -> {
      if (ip.ip_ok) {
        false
      } else {
        gn_dns_eq q s hg;
        rewrite (arel true d_GeneralName q g hg) as (gn_dns_m q s hg);
        dns_open q s hg;
        with w. assert (S.pts_to s #q w);
        S.pts_to_len s;
        let n = copy_slice s nb nblen;
        let r = (if SZ.gt n 0sz then true else false);
        if r {
          with dn'. assert (A.pts_to nb dn');
          A.pts_to_len nb;
          cb_slice dn' n w;
          let m = N.dns_matches nb n 0sz n h hlen;
          dns_close q s hg;
          rewrite (gn_dns_m q s hg) as (arel true d_GeneralName q g hg);
          m
        } else {
          dns_close q s hg;
          rewrite (gn_dns_m q s hg) as (arel true d_GeneralName q g hg);
          false
        }
      }
    }
    GeneralName_iPAddress s -> {
      if (ip.ip_ok) {
        gn_ip_eq q s hg;
        rewrite (arel true d_GeneralName q g hg) as (gn_ip_m q s hg);
        ip_open q s hg;
        with w. assert (S.pts_to s #q w);
        S.pts_to_len s;
        let n = copy_slice s nb nblen;
        let r = (if SZ.gt n 0sz then true else false);
        if r {
          with dn'. assert (A.pts_to nb dn');
          A.pts_to_len nb;
          cb_slice dn' n w;
          let m = N.ip_is nb n ip;
          ip_close q s hg;
          rewrite (gn_ip_m q s hg) as (arel true d_GeneralName q g hg);
          m
        } else {
          ip_close q s hg;
          rewrite (gn_ip_m q s hg) as (arel true d_GeneralName q g hg);
          false
        }
      } else {
        false
      }
    }
    _ -> {
      false
    }
  }
}
#pop-options

#push-options "--z3rlimit 80 --fuel 2 --ifuel 2"
(** [C.names_match] over the GeneralNames at [input], failing closed. *)
fn gns_ok (input: S.slice U8.t) (count: SZ.t) (#q: perm) (#w: Ghost.erased (Seq.seq U8.t))
  (#l: Ghost.erased (list (asn1_t X.k_GeneralName)))
  (h: A.array U8.t) (hlen: SZ.t) (#hb: Ghost.erased (Seq.seq U8.t)) (ip: N.ip_v)
  (nb: A.array U8.t) (nblen: SZ.t) (#dn: Ghost.erased (Seq.seq U8.t))
  requires S.pts_to input #q w ** A.pts_to h hb ** A.pts_to nb dn **
           pure (nl_at X.k_GeneralName w 0 (SZ.v count) l /\ host_ok hb hlen ip /\ scratch_ok dn nb nblen)
  returns r: bool
  ensures S.pts_to input #q w ** A.pts_to h hb ** (exists* dn'. A.pts_to nb dn' **
          pure (scratch_ok dn' nb nblen /\ (r ==> C.names_match (F.cb hb hlen) (N.to_ip ip) l)))
{
  let mut off = 0sz;
  let mut i = count;
  let mut fin = false;
  nl_rest_eq X.k_GeneralName w 0 (SZ.v count) l;
  while (let vi = !i; let vf = !fin; (not vf && SZ.gt vi 0sz))
  invariant exists* (voff vi: SZ.t) (vf: bool) (dn': Seq.seq U8.t).
    pts_to off voff ** pts_to i vi ** pts_to fin vf ** S.pts_to input #q w **
    A.pts_to h hb ** A.pts_to nb dn' **
    pure (scratch_ok dn' nb nblen /\
          (vf ==> C.names_match (F.cb hb hlen) (N.to_ip ip) l) /\
          (not vf ==> nl_at X.k_GeneralName w (SZ.v voff) (SZ.v vi) (nl_rest X.k_GeneralName w (SZ.v voff) (SZ.v vi)) /\
                      (C.names_match (F.cb hb hlen) (N.to_ip ip) (nl_rest X.k_GeneralName w (SZ.v voff) (SZ.v vi)) ==>
                       C.names_match (F.cb hb hlen) (N.to_ip ip) l)))
  decreases ((if !fin then 0 else 1) + SZ.v (!i))
  {
    let vi = !i;
    let voff = !off;
    let p = nl_elem validate_GeneralName parse_GeneralName input voff (SZ.v vi - 1) #q #w
      #(nl_rest X.k_GeneralName w (SZ.v voff) (SZ.v vi));
    let x = fst p;
    with hg. assert (arel true d_GeneralName q (fst p) hg);
    rewrite each (fst p) as x;
    let hit = gn_ok x h hlen ip nb nblen;
    elim_trade (arel true d_GeneralName q x hg) (S.pts_to input #q w);
    if hit {
      fin := true;
    } else {
      nl_rest_eq X.k_GeneralName w (SZ.v (snd p)) (SZ.v vi - 1) (L.tl (nl_rest X.k_GeneralName w (SZ.v voff) (SZ.v vi)));
      off := snd p;
      i := SZ.sub vi 1sz;
    }
  };
  let vf = !fin;
  vf
}
#pop-options

(** [d[0, len)] is GeneralNames naming the host, failing closed. *)
fn san_ok (buf: A.array U8.t) (#p: perm) (#d: Ghost.erased (Seq.seq U8.t)) (len: SZ.t{SZ.v len <= Seq.length d})
  (h: A.array U8.t) (hlen: SZ.t) (#hb: Ghost.erased (Seq.seq U8.t)) (ip: N.ip_v)
  (nb: A.array U8.t) (nblen: SZ.t) (#dn: Ghost.erased (Seq.seq U8.t))
  requires A.pts_to buf #p d ** A.pts_to h hb ** A.pts_to nb dn **
           pure (host_ok hb hlen ip /\ scratch_ok dn nb nblen)
  returns r: bool
  ensures A.pts_to buf #p d ** A.pts_to h hb ** (exists* dn'. A.pts_to nb dn' **
          pure (scratch_ok dn' nb nblen /\
                (r ==> (match XP.parse_full X.k_GeneralNames (Seq.slice d 0 (SZ.v len)) with
                        | Some gs -> C.names_match (F.cb hb hlen) (N.to_ip ip) gs
                        | None -> false))))
{
  let s = prefix_slice buf #p #d len;
  let o = open_whole validate_GeneralNames parse_GeneralNames s;
  match o {
    None -> {
      unfold (whole_res d_GeneralNames p s (Seq.slice d 0 (SZ.v len)) None);
      elim_trade (S.pts_to s #p (Seq.slice d 0 (SZ.v len))) (A.pts_to buf #p d);
      false
    }
    Some x -> {
      unfold (whole_res d_GeneralNames p s (Seq.slice d 0 (SZ.v len)) (Some x));
      with v. assert (arel true d_GeneralNames p x v);
      gns_eq p x v;
      let vl : Ghost.erased (list (asn1_t X.k_GeneralName)) = Ghost.elift1 (fun (y: asn1_t X.k_GeneralNames) -> (y <: list (asn1_t X.k_GeneralName))) v;
      rewrite (arel true d_GeneralNames p x v) as (PS.ml_match d_GeneralName p x vl);
      let it = ml_open d_GeneralName x #p #vl;
      with q w. assert (S.pts_to (fst it) #q w);
      let ok = gns_ok (fst it) (snd it) #q #w #vl h hlen ip nb nblen;
      elim_trade (S.pts_to (fst it) #q w) (PS.ml_match d_GeneralName p x vl);
      rewrite (PS.ml_match d_GeneralName p x vl) as (arel true d_GeneralNames p x v);
      elim_trade (arel true d_GeneralNames p x v) (S.pts_to s #p (Seq.slice d 0 (SZ.v len)));
      elim_trade (S.pts_to s #p (Seq.slice d 0 (SZ.v len))) (A.pts_to buf #p d);
      ok
    }
  }
}
