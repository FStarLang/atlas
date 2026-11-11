module TLS13.Impl.X509.Check

(** The per-certificate checks of [TLS13.X509.Chain] -- [path_ok],
    [leaf_ok], [issuer_ok], [names_issuer] and [signed_by] -- over DER
    certificates parsed by the everparse-asn1 parser of [src/asn1/X509.asn].
    Each fails closed: [r ==> spec]. *)

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
module Ex = TLS13.Impl.X509.Exts
module F = TLS13.Impl.X509.Fields
module I64 = FStar.Int64
module CL = TLS13.ConnectionLog
module Cr = TLS13.Crypto
module CS = TLS13.Crypto.Spec
module K = TLS13.Impl.X509.Key
module KS = TLS13.X509.KeySpec
module N = TLS13.Impl.X509.Names
module PK = TLS13.Impl.X509.PublicKey
module PS = ASN1.Pulse.ParseSeqOf
module S = Pulse.Lib.Slice
module Ser = ASN1.Spec.Serializer
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module Va = TLS13.Impl.X509.Values
module VE = ASN1.Spec.Value.Enc
module X = TLS13.Wire.Generated.X509
module XP = TLS13.X509.Profile

(** {2 Extensions} *)

let ext_opt (pm: perm) (e: t_TBSCertificate_extensions_opt) (y: XP.tbs) : slprop =
  prel_option (arel true (D_ILC (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 3) (CD_PREFIXED d_Extensions)))
    pm (oview_TBSCertificate_extensions e) (XP.tbs_extensions y)

(** A scratch buffer for an extension value. *)
let scratch (d: Seq.seq U8.t) (buf: A.array U8.t) (blen: SZ.t) : prop =
  Seq.length d == SZ.v blen /\ A.length buf == SZ.v blen

fn exts_find (e: t_TBSCertificate_extensions_opt) (#pm: perm) (#y: Ghost.erased XP.tbs) (k: U8.t)
  (buf: A.array U8.t) (blen: SZ.t) (#old: Ghost.erased (Seq.seq U8.t))
  requires ext_opt pm e y ** A.pts_to buf old ** pure (scratch old buf blen)
  returns r: Ex.found
  ensures ext_opt pm e y ** (exists* d. A.pts_to buf d **
          pure (scratch d buf blen /\ Ex.found_ok r (C.find_extension (C.exts y) k) d))
{
  unfold ext_opt;
  match e {
    TBSCertificate_extensions_absent -> {
      rewrite (prel_option (arel true (D_ILC (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 3) (CD_PREFIXED d_Extensions)))
                 pm (oview_TBSCertificate_extensions e) (XP.tbs_extensions y))
           as (prel_option (arel true (D_ILC (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 3) (CD_PREFIXED d_Extensions)))
                 pm None (XP.tbs_extensions y));
      opt_none_elim (arel true (D_ILC (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 3) (CD_PREFIXED d_Extensions)))
        pm (XP.tbs_extensions y);
      rewrite (prel_option (arel true (D_ILC (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 3) (CD_PREFIXED d_Extensions)))
                 pm None (XP.tbs_extensions y))
           as (prel_option (arel true (D_ILC (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 3) (CD_PREFIXED d_Extensions)))
                 pm (oview_TBSCertificate_extensions e) (XP.tbs_extensions y));
      fold (ext_opt pm e y);
      ({ Ex.fd_ok = true; Ex.fd_some = false; Ex.fd_len = 0sz } <: Ex.found)
    }
    TBSCertificate_extensions_present el -> {
      rewrite (prel_option (arel true (D_ILC (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 3) (CD_PREFIXED d_Extensions)))
                 pm (oview_TBSCertificate_extensions e) (XP.tbs_extensions y))
           as (prel_option (arel true (D_ILC (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 3) (CD_PREFIXED d_Extensions)))
                 pm (Some el) (XP.tbs_extensions y));
      let b = opt_some_elim (arel true (D_ILC (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 3) (CD_PREFIXED d_Extensions)))
                pm el (XP.tbs_extensions y);
      exts_eq pm el b;
      let bl : Ghost.erased (list XP.extension) = Ghost.elift1 (fun (z: sized_list true XP.extension) -> (z <: list XP.extension)) b;
      rewrite (arel true (D_ILC (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 3) (CD_PREFIXED d_Extensions)) pm el b)
           as (PS.ml_match d_Extension pm el bl);
      let it = ml_open d_Extension el #pm #bl;
      with q w. assert (S.pts_to (fst it) #q w);
      let r = Ex.find_ext (fst it) (snd it) #q #w #bl k buf blen;
      elim_trade (S.pts_to (fst it) #q w) (PS.ml_match d_Extension pm el bl);
      rewrite (PS.ml_match d_Extension pm el bl)
           as (arel true (D_ILC (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 3) (CD_PREFIXED d_Extensions)) pm el b);
      opt_some_intro (arel true (D_ILC (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 3) (CD_PREFIXED d_Extensions)))
        pm el b (XP.tbs_extensions y);
      rewrite (prel_option (arel true (D_ILC (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 3) (CD_PREFIXED d_Extensions)))
                 pm (Some el) (XP.tbs_extensions y))
           as (prel_option (arel true (D_ILC (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 3) (CD_PREFIXED d_Extensions)))
                 pm (oview_TBSCertificate_extensions e) (XP.tbs_extensions y));
      fold (ext_opt pm e y);
      r
    }
  }
}

fn exts_check (e: t_TBSCertificate_extensions_opt) (#pm: perm) (#y: Ghost.erased XP.tbs)
  requires ext_opt pm e y
  returns r: bool
  ensures ext_opt pm e y ** pure (r ==> C.extensions_ok (C.exts y))
{
  unfold ext_opt;
  match e {
    TBSCertificate_extensions_absent -> {
      rewrite (prel_option (arel true (D_ILC (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 3) (CD_PREFIXED d_Extensions)))
                 pm (oview_TBSCertificate_extensions e) (XP.tbs_extensions y))
           as (prel_option (arel true (D_ILC (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 3) (CD_PREFIXED d_Extensions)))
                 pm None (XP.tbs_extensions y));
      opt_none_elim (arel true (D_ILC (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 3) (CD_PREFIXED d_Extensions)))
        pm (XP.tbs_extensions y);
      rewrite (prel_option (arel true (D_ILC (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 3) (CD_PREFIXED d_Extensions)))
                 pm None (XP.tbs_extensions y))
           as (prel_option (arel true (D_ILC (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 3) (CD_PREFIXED d_Extensions)))
                 pm (oview_TBSCertificate_extensions e) (XP.tbs_extensions y));
      fold (ext_opt pm e y);
      assert (pure (C.extensions_ok []));
      true
    }
    TBSCertificate_extensions_present el -> {
      rewrite (prel_option (arel true (D_ILC (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 3) (CD_PREFIXED d_Extensions)))
                 pm (oview_TBSCertificate_extensions e) (XP.tbs_extensions y))
           as (prel_option (arel true (D_ILC (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 3) (CD_PREFIXED d_Extensions)))
                 pm (Some el) (XP.tbs_extensions y));
      let b = opt_some_elim (arel true (D_ILC (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 3) (CD_PREFIXED d_Extensions)))
                pm el (XP.tbs_extensions y);
      exts_eq pm el b;
      let bl : Ghost.erased (list XP.extension) = Ghost.elift1 (fun (z: sized_list true XP.extension) -> (z <: list XP.extension)) b;
      rewrite (arel true (D_ILC (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 3) (CD_PREFIXED d_Extensions)) pm el b)
           as (PS.ml_match d_Extension pm el bl);
      let it = ml_open d_Extension el #pm #bl;
      with q w. assert (S.pts_to (fst it) #q w);
      let r = Ex.exts_ok (fst it) (snd it) #q #w #bl;
      elim_trade (S.pts_to (fst it) #q w) (PS.ml_match d_Extension pm el bl);
      rewrite (PS.ml_match d_Extension pm el bl)
           as (arel true (D_ILC (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 3) (CD_PREFIXED d_Extensions)) pm el b);
      opt_some_intro (arel true (D_ILC (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 3) (CD_PREFIXED d_Extensions)))
        pm el b (XP.tbs_extensions y);
      rewrite (prel_option (arel true (D_ILC (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 3) (CD_PREFIXED d_Extensions)))
                 pm (Some el) (XP.tbs_extensions y))
           as (prel_option (arel true (D_ILC (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 3) (CD_PREFIXED d_Extensions)))
                 pm (oview_TBSCertificate_extensions e) (XP.tbs_extensions y));
      fold (ext_opt pm e y);
      r
    }
  }
}

fn tbs_find (x: t_TBSCertificate) (#pm: perm) (#y: Ghost.erased XP.tbs) (k: U8.t)
  (buf: A.array U8.t) (blen: SZ.t) (#old: Ghost.erased (Seq.seq U8.t))
  requires tbs_rel pm x y ** A.pts_to buf old ** pure (scratch old buf blen)
  returns r: Ex.found
  ensures tbs_rel pm x y ** (exists* d. A.pts_to buf d **
          pure (scratch d buf blen /\ Ex.found_ok r (C.find_extension (C.exts y) k) d))
{
  unfold tbs_rel;
  rewrite (prel_option (arel true (D_ILC (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 3) (CD_PREFIXED d_Extensions)))
             pm (oview_TBSCertificate_extensions x.extensions) (snd (snd (snd (snd (snd (snd (snd (snd (snd (reveal y)))))))))))
       as (ext_opt pm x.extensions y);
  let r = exts_find x.extensions k buf blen;
  rewrite (ext_opt pm x.extensions y)
       as (prel_option (arel true (D_ILC (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 3) (CD_PREFIXED d_Extensions)))
             pm (oview_TBSCertificate_extensions x.extensions) (snd (snd (snd (snd (snd (snd (snd (snd (snd (reveal y)))))))))));
  fold (tbs_rel pm x y);
  r
}

fn tbs_exts_ok (x: t_TBSCertificate) (#pm: perm) (#y: Ghost.erased XP.tbs)
  requires tbs_rel pm x y
  returns r: bool
  ensures tbs_rel pm x y ** pure (r ==> C.extensions_ok (C.exts y))
{
  unfold tbs_rel;
  rewrite (prel_option (arel true (D_ILC (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 3) (CD_PREFIXED d_Extensions)))
             pm (oview_TBSCertificate_extensions x.extensions) (snd (snd (snd (snd (snd (snd (snd (snd (snd (reveal y)))))))))))
       as (ext_opt pm x.extensions y);
  let r = exts_check x.extensions;
  rewrite (ext_opt pm x.extensions y)
       as (prel_option (arel true (D_ILC (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 3) (CD_PREFIXED d_Extensions)))
             pm (oview_TBSCertificate_extensions x.extensions) (snd (snd (snd (snd (snd (snd (snd (snd (snd (reveal y)))))))))));
  fold (tbs_rel pm x y);
  r
}

(** {2 Version} *)

let ver_accept (v: t_TBSCertificate_version_opt) : bool =
  match v with
  | TBSCertificate_version_present (Small i) -> i = 2L
  | _ -> false

#push-options "--ifuel 2 --z3rlimit 40"
ghost fn ver_info (pm: perm) (v: t_TBSCertificate_version_opt) (y: XP.tbs)
  requires ver_m pm v y ** pure (ver_accept v)
  ensures ver_m pm v y ** pure (C.is_v3 y)
{
  if (Default? (XP.tbs_version y)) {
    rewrite (ver_m pm v y) as pure False;
    unreachable ()
  } else {
    rewrite (ver_m pm v y)
         as (asn1_int_rel asn1_any_integer_bound pm (TBSCertificate_version_present?.v v) (Nondefault?.v' (XP.tbs_version y)));
    rewrite (asn1_int_rel asn1_any_integer_bound pm (TBSCertificate_version_present?.v v) (Nondefault?.v' (XP.tbs_version y)))
         as pure ((I64.v (Small?._0 (TBSCertificate_version_present?.v v)) <: int) == (Nondefault?.v' (XP.tbs_version y) <: int));
    rewrite pure ((I64.v (Small?._0 (TBSCertificate_version_present?.v v)) <: int) == (Nondefault?.v' (XP.tbs_version y) <: int))
         as (asn1_int_rel asn1_any_integer_bound pm (TBSCertificate_version_present?.v v) (Nondefault?.v' (XP.tbs_version y)));
    rewrite (asn1_int_rel asn1_any_integer_bound pm (TBSCertificate_version_present?.v v) (Nondefault?.v' (XP.tbs_version y)))
         as (ver_m pm v y)
  }
}
#pop-options

fn tbs_v3 (x: t_TBSCertificate) (#pm: perm) (#y: Ghost.erased XP.tbs)
  requires tbs_rel pm x y
  returns r: bool
  ensures tbs_rel pm x y ** pure (r ==> C.is_v3 y)
{
  unfold tbs_rel;
  ver_eq pm x.version y;
  rewrite (ver_rel pm x.version (fst (reveal y))) as (ver_m pm x.version y);
  let r = ver_accept x.version;
  if r {
    ver_info pm x.version y
  };
  rewrite (ver_m pm x.version y) as (ver_rel pm x.version (fst (reveal y)));
  fold (tbs_rel pm x y);
  r
}

(** {2 Algorithms} *)

let params_same_spec (a b: option asn1_value) : GTot bool =
  match a, b with
  | None, None -> true
  | Some p, Some q -> Seq.eq (VE.asn1_value_enc p) (VE.asn1_value_enc q)
  | _ -> false

fn params_same (a: t_AlgorithmIdentifier_parameters_opt) (#pa: perm) (#ya: Ghost.erased (option asn1_value))
  (b: t_AlgorithmIdentifier_parameters_opt) (#pb: perm) (#yb: Ghost.erased (option asn1_value))
  requires prel_option any_rel pa (oview_AlgorithmIdentifier_parameters a) ya **
           prel_option any_rel pb (oview_AlgorithmIdentifier_parameters b) yb
  returns r: bool
  ensures prel_option any_rel pa (oview_AlgorithmIdentifier_parameters a) ya **
          prel_option any_rel pb (oview_AlgorithmIdentifier_parameters b) yb **
          pure (r ==> params_same_spec ya yb)
{
  match a {
    AlgorithmIdentifier_parameters_absent -> {
      match b {
        AlgorithmIdentifier_parameters_absent -> {
          rewrite (prel_option any_rel pa (oview_AlgorithmIdentifier_parameters a) ya) as (prel_option any_rel pa None ya);
          rewrite (prel_option any_rel pb (oview_AlgorithmIdentifier_parameters b) yb) as (prel_option any_rel pb None yb);
          opt_none_elim any_rel pa ya;
          opt_none_elim any_rel pb yb;
          rewrite (prel_option any_rel pa None ya) as (prel_option any_rel pa (oview_AlgorithmIdentifier_parameters a) ya);
          rewrite (prel_option any_rel pb None yb) as (prel_option any_rel pb (oview_AlgorithmIdentifier_parameters b) yb);
          true
        }
        AlgorithmIdentifier_parameters_present _ -> {
          false
        }
      }
    }
    AlgorithmIdentifier_parameters_present ps -> {
      match b {
        AlgorithmIdentifier_parameters_absent -> {
          false
        }
        AlgorithmIdentifier_parameters_present qs -> {
          rewrite (prel_option any_rel pa (oview_AlgorithmIdentifier_parameters a) ya) as (prel_option any_rel pa (Some ps) ya);
          rewrite (prel_option any_rel pb (oview_AlgorithmIdentifier_parameters b) yb) as (prel_option any_rel pb (Some qs) yb);
          let va = opt_some_elim any_rel pa ps ya;
          let vb = opt_some_elim any_rel pb qs yb;
          unfold (any_rel pa ps va);
          unfold (any_rel pb qs vb);
          unfold (prel_slice_ser VE.asn1_value_enc pa ps va);
          unfold (prel_slice_ser VE.asn1_value_enc pb qs vb);
          let r = slice_eq ps qs;
          fold (prel_slice_ser VE.asn1_value_enc pa ps va);
          fold (prel_slice_ser VE.asn1_value_enc pb qs vb);
          fold (any_rel pa ps va);
          fold (any_rel pb qs vb);
          opt_some_intro any_rel pa ps va ya;
          opt_some_intro any_rel pb qs vb yb;
          rewrite (prel_option any_rel pa (Some ps) ya) as (prel_option any_rel pa (oview_AlgorithmIdentifier_parameters a) ya);
          rewrite (prel_option any_rel pb (Some qs) yb) as (prel_option any_rel pb (oview_AlgorithmIdentifier_parameters b) yb);
          r
        }
      }
    }
  }
}

fn alg_same (a: t_AlgorithmIdentifier) (#pa: perm) (#va: Ghost.erased XP.alg_id)
  (b: t_AlgorithmIdentifier) (#pb: perm) (#vb: Ghost.erased XP.alg_id)
  requires arel true d_AlgorithmIdentifier pa a va ** arel true d_AlgorithmIdentifier pb b vb
  returns r: bool
  ensures arel true d_AlgorithmIdentifier pa a va ** arel true d_AlgorithmIdentifier pb b vb **
          pure (r ==> C.alg_same va vb)
{
  alg_eq pa a va;
  alg_eq pb b vb;
  rewrite (arel true d_AlgorithmIdentifier pa a va) as (alg_rel pa a va);
  rewrite (arel true d_AlgorithmIdentifier pb b vb) as (alg_rel pb b vb);
  unfold (alg_rel pa a va);
  unfold (alg_rel pb b vb);
  unfold (oid_rel pa a.algorithm (fst (reveal va)));
  unfold (oid_rel pb b.algorithm (fst (reveal vb)));
  unfold (prel_slice_ser (E.leaf_enc ASN1_OID) pa a.algorithm (fst (reveal va)));
  unfold (prel_slice_ser (E.leaf_enc ASN1_OID) pb b.algorithm (fst (reveal vb)));
  let r1 = slice_eq a.algorithm b.algorithm;
  fold (prel_slice_ser (E.leaf_enc ASN1_OID) pa a.algorithm (fst (reveal va)));
  fold (prel_slice_ser (E.leaf_enc ASN1_OID) pb b.algorithm (fst (reveal vb)));
  fold (oid_rel pa a.algorithm (fst (reveal va)));
  fold (oid_rel pb b.algorithm (fst (reveal vb)));
  let r2 = params_same a.parameters b.parameters;
  fold (alg_rel pa a va);
  fold (alg_rel pb b vb);
  rewrite (alg_rel pa a va) as (arel true d_AlgorithmIdentifier pa a va);
  rewrite (alg_rel pb b vb) as (arel true d_AlgorithmIdentifier pb b vb);
  (r1 && r2)
}

fn tbs_alg_same (x: t_TBSCertificate) (#pm: perm) (#y: Ghost.erased XP.tbs)
  (a: t_AlgorithmIdentifier) (#pa: perm) (#va: Ghost.erased XP.alg_id)
  requires tbs_rel pm x y ** arel true d_AlgorithmIdentifier pa a va
  returns r: bool
  ensures tbs_rel pm x y ** arel true d_AlgorithmIdentifier pa a va ** pure (r ==> C.alg_same va (XP.tbs_sig_alg y))
{
  unfold tbs_rel;
  let r = alg_same a x.signature;
  fold (tbs_rel pm x y);
  r
}

(** {2 Validity} *)

ghost fn utc_open (pm: perm) (s: S.slice U8.t) (y: asn1_t X.k_Time)
  requires time_m pm (Time_utcTime s) y
  ensures exists* w. S.pts_to s #pm w **
          pure (dfst y == C.id_utc_time /\ w == E.leaf_enc ASN1_UTCTIME (C.time_utc y))
{
  if (dfst y = C.id_utc_time) {
    rewrite (time_m pm (Time_utcTime s) y) as (prel_slice_ser (E.leaf_enc ASN1_UTCTIME) pm s (C.time_utc y));
    unfold (prel_slice_ser (E.leaf_enc ASN1_UTCTIME) pm s (C.time_utc y))
  } else {
    rewrite (time_m pm (Time_utcTime s) y) as pure False;
    unreachable ()
  }
}

ghost fn utc_close (pm: perm) (s: S.slice U8.t) (y: asn1_t X.k_Time) (#w: Seq.seq U8.t)
  requires S.pts_to s #pm w ** pure (dfst y == C.id_utc_time /\ w == E.leaf_enc ASN1_UTCTIME (C.time_utc y))
  ensures time_m pm (Time_utcTime s) y
{
  fold (prel_slice_ser (E.leaf_enc ASN1_UTCTIME) pm s (C.time_utc y));
  rewrite (prel_slice_ser (E.leaf_enc ASN1_UTCTIME) pm s (C.time_utc y)) as (time_m pm (Time_utcTime s) y)
}

ghost fn gen_open (pm: perm) (s: S.slice U8.t) (y: asn1_t X.k_Time)
  requires time_m pm (Time_generalTime s) y
  ensures exists* w. S.pts_to s #pm w **
          pure (dfst y == C.id_generalized_time /\ w == E.leaf_enc ASN1_GENERALIZEDTIME (C.time_generalized y))
{
  if (dfst y = C.id_generalized_time) {
    rewrite (time_m pm (Time_generalTime s) y)
         as (prel_slice_ser (E.leaf_enc ASN1_GENERALIZEDTIME) pm s (C.time_generalized y));
    unfold (prel_slice_ser (E.leaf_enc ASN1_GENERALIZEDTIME) pm s (C.time_generalized y))
  } else {
    rewrite (time_m pm (Time_generalTime s) y) as pure False;
    unreachable ()
  }
}

ghost fn gen_close (pm: perm) (s: S.slice U8.t) (y: asn1_t X.k_Time) (#w: Seq.seq U8.t)
  requires S.pts_to s #pm w **
           pure (dfst y == C.id_generalized_time /\ w == E.leaf_enc ASN1_GENERALIZEDTIME (C.time_generalized y))
  ensures time_m pm (Time_generalTime s) y
{
  fold (prel_slice_ser (E.leaf_enc ASN1_GENERALIZEDTIME) pm s (C.time_generalized y));
  rewrite (prel_slice_ser (E.leaf_enc ASN1_GENERALIZEDTIME) pm s (C.time_generalized y))
       as (time_m pm (Time_generalTime s) y)
}

let id_distinct () : Lemma (C.id_utc_time <> C.id_generalized_time) =
  assert_norm (C.id_utc_time <> C.id_generalized_time)

(** The time [w] (GeneralizedTime if [gen], else UTCTime) in seconds. *)
fn time_bytes (s: S.slice U8.t) (#pm: perm) (#w: Ghost.erased (Seq.seq U8.t)) (gen: bool)
  requires S.pts_to s #pm w
  returns r: F.time_value
  ensures S.pts_to s #pm w **
          pure (r.t_ok ==> (if gen then C.generalized_time w else C.utc_time w) == Some (U64.v r.t_val))
{
  let buf = A.alloc 0uy 24sz;
  let n = copy_slice s buf 24sz;
  with d. assert (A.pts_to buf d);
  if (SZ.gt n 0sz) {
    Va.cb_slice d n w;
    let t = F.time_of buf n gen;
    A.free buf;
    t
  } else {
    A.free buf;
    F.no_time
  }
}

fn time_get (x: t_Time) (#pm: perm) (#y: Ghost.erased (asn1_t X.k_Time))
  requires arel true d_Time pm x y
  returns r: F.time_value
  ensures arel true d_Time pm x y ** pure (r.t_ok ==> C.time_value y == Some (U64.v r.t_val))
{
  time_eq pm x y;
  rewrite (arel true d_Time pm x y) as (time_m pm x y);
  id_distinct ();
  match x {
    Time_utcTime s -> {
      rewrite (time_m pm x y) as (time_m pm (Time_utcTime s) y);
      utc_open pm s y;
      let r = time_bytes s false;
      utc_close pm s y;
      rewrite (time_m pm (Time_utcTime s) y) as (time_m pm x y);
      rewrite (time_m pm x y) as (arel true d_Time pm x y);
      r
    }
    Time_generalTime s -> {
      rewrite (time_m pm x y) as (time_m pm (Time_generalTime s) y);
      gen_open pm s y;
      let r = time_bytes s true;
      gen_close pm s y;
      rewrite (time_m pm (Time_generalTime s) y) as (time_m pm x y);
      rewrite (time_m pm x y) as (arel true d_Time pm x y);
      r
    }
  }
}

fn tbs_valid (x: t_TBSCertificate) (#pm: perm) (#y: Ghost.erased XP.tbs) (now: U64.t)
  requires tbs_rel pm x y
  returns r: bool
  ensures tbs_rel pm x y ** pure (r ==> C.valid_at y (U64.v now))
{
  unfold tbs_rel;
  with yv. assert (arel true d_Validity pm x.validity yv);
  validity_eq pm x.validity yv;
  rewrite (arel true d_Validity pm x.validity yv) as (validity_rel pm x.validity yv);
  unfold validity_rel;
  let nb = time_get x.validity.notBefore;
  let na = time_get x.validity.notAfter;
  fold (validity_rel pm x.validity yv);
  rewrite (validity_rel pm x.validity yv) as (arel true d_Validity pm x.validity yv);
  fold (tbs_rel pm x y);
  (nb.t_ok && na.t_ok && U64.lte nb.t_val now && U64.lte now na.t_val)
}

(** {2 Names} *)

let half_pos (p: perm) : Lemma (p /. 2.0R >. 0.0R) = ()

ghost fn name_open (pm: perm) (a: t_Name_kept) (y: XP.name) (sa: S.slice U8.t)
  requires arel true d_Name pm a y ** pure (a.raw == Name_raw_present sa)
  ensures S.pts_to sa #(pm /. 2.0R) (C.name_bytes y) **
          trade (S.pts_to sa #(pm /. 2.0R) (C.name_bytes y)) (arel true d_Name pm a y)
{
  name_eq pm a y;
  rewrite (arel true d_Name pm a y) as (name_rel pm a y);
  unfold (name_rel pm a y);
  half_pos pm;
  rewrite (keep_rel X.k_Name (pm /. 2.0R) (kview_Name a).kraw y) as (keep_rel X.k_Name (pm /. 2.0R) (Some sa) y);
  unfold (keep_rel X.k_Name (pm /. 2.0R) (Some sa) y);
  unfold (prel_slice_ser (Ser.asn1_enc X.k_Name) (pm /. 2.0R) sa y);
  intro_trade (S.pts_to sa #(pm /. 2.0R) (C.name_bytes y)) (arel true d_Name pm a y)
    (arel true dbase_Name (pm /. 2.0R) a.value y ** pure (Ser.encodable X.k_Name y /\ a.raw == Name_raw_present sa)) fn _ {
    fold (prel_slice_ser (Ser.asn1_enc X.k_Name) (pm /. 2.0R) sa y);
    fold (keep_rel X.k_Name (pm /. 2.0R) (Some sa) y);
    rewrite (keep_rel X.k_Name (pm /. 2.0R) (Some sa) y) as (keep_rel X.k_Name (pm /. 2.0R) (kview_Name a).kraw y);
    fold (name_rel pm a y);
    name_eq pm a y;
    rewrite (name_rel pm a y) as (arel true d_Name pm a y)
  }
}

fn name_same (a: t_Name_kept) (#pa: perm) (#ya: Ghost.erased XP.name)
  (b: t_Name_kept) (#pb: perm) (#yb: Ghost.erased XP.name)
  requires arel true d_Name pa a ya ** arel true d_Name pb b yb
  returns r: bool
  ensures arel true d_Name pa a ya ** arel true d_Name pb b yb **
          pure (r ==> Seq.eq (C.name_bytes ya) (C.name_bytes yb))
{
  let ra = a.raw;
  let rb = b.raw;
  match ra {
    Name_raw_absent -> {
      false
    }
    Name_raw_present sa -> {
      match rb {
        Name_raw_absent -> {
          false
        }
        Name_raw_present sb -> {
          name_open pa a ya sa;
          name_open pb b yb sb;
          let r = slice_eq sa sb;
          elim_trade (S.pts_to sa #(pa /. 2.0R) (C.name_bytes ya)) (arel true d_Name pa a ya);
          elim_trade (S.pts_to sb #(pb /. 2.0R) (C.name_bytes yb)) (arel true d_Name pb b yb);
          r
        }
      }
    }
  }
}

(** {2 Extension values} *)

fn tbs_eku (x: t_TBSCertificate) (#pm: perm) (#y: Ghost.erased XP.tbs)
  (buf: A.array U8.t) (blen: SZ.t) (#old: Ghost.erased (Seq.seq U8.t))
  requires tbs_rel pm x y ** A.pts_to buf old ** pure (scratch old buf blen)
  returns r: bool
  ensures tbs_rel pm x y ** (exists* d. A.pts_to buf d ** pure (scratch d buf blen)) **
          pure (r ==> C.ext_key_usage_ok (C.exts y))
{
  let f = tbs_find x C.oid_ext_key_usage buf blen;
  with d. assert (A.pts_to buf d);
  if (f.fd_ok) {
    if (f.fd_some) {
      Va.eku_ok buf f.fd_len
    } else {
      true
    }
  } else {
    false
  }
}

fn tbs_ku (x: t_TBSCertificate) (#pm: perm) (#y: Ghost.erased XP.tbs) (mask: U8.t)
  (buf: A.array U8.t) (blen: SZ.t) (#old: Ghost.erased (Seq.seq U8.t))
  requires tbs_rel pm x y ** A.pts_to buf old ** pure (scratch old buf blen)
  returns r: bool
  ensures tbs_rel pm x y ** (exists* d. A.pts_to buf d ** pure (scratch d buf blen)) **
          pure (r ==> C.key_usage_allows (C.exts y) mask)
{
  let f = tbs_find x C.oid_key_usage buf blen;
  with d. assert (A.pts_to buf d);
  if (f.fd_ok) {
    if (f.fd_some) {
      Va.ku_ok buf f.fd_len mask
    } else {
      true
    }
  } else {
    false
  }
}

let bc_spec (l: list XP.extension) (below: nat) : GTot bool =
  match C.find_extension l C.oid_basic_constraints with
  | Some v -> C.ca_allows v below
  | None -> false

(** [issuer_ok] if [issuer]. *)
fn tbs_issuer (x: t_TBSCertificate) (#pm: perm) (#y: Ghost.erased XP.tbs) (issuer: bool) (below: U32.t)
  (buf: A.array U8.t) (blen: SZ.t) (#old: Ghost.erased (Seq.seq U8.t))
  requires tbs_rel pm x y ** A.pts_to buf old ** pure (scratch old buf blen)
  returns r: bool
  ensures tbs_rel pm x y ** (exists* d. A.pts_to buf d ** pure (scratch d buf blen)) **
          pure (r ==> (issuer ==> bc_spec (C.exts y) (U32.v below) /\ C.key_usage_allows (C.exts y) 0x04uy))
{
  if (not issuer) {
    true
  } else {
    let f = tbs_find x C.oid_basic_constraints buf blen;
    with d. assert (A.pts_to buf d);
    if (f.fd_ok && f.fd_some) {
      let bc = Va.bc_ok buf f.fd_len below;
      if bc {
        tbs_ku x 0x04uy buf blen
      } else {
        false
      }
    } else {
      false
    }
  }
}

(** [leaf_ok] for the host [cb hb hlen] if [leaf]. *)
fn tbs_leaf (x: t_TBSCertificate) (#pm: perm) (#y: Ghost.erased XP.tbs) (leaf: bool)
  (h: A.array U8.t) (hlen: SZ.t) (#hb: Ghost.erased (Seq.seq U8.t))
  (buf: A.array U8.t) (blen: SZ.t) (#old: Ghost.erased (Seq.seq U8.t))
  requires tbs_rel pm x y ** A.pts_to h hb ** A.pts_to buf old ** pure (scratch old buf blen /\ F.ok_len hb hlen)
  returns r: bool
  ensures tbs_rel pm x y ** A.pts_to h hb ** (exists* d. A.pts_to buf d ** pure (scratch d buf blen)) **
          pure (r ==> (leaf ==> C.subject_alt_name_ok (C.exts y) (F.cb hb hlen) /\
                                C.key_usage_allows (C.exts y) 0x80uy))
{
  if (not leaf) {
    true
  } else if (hlen = 0sz) {
    false
  } else {
    let ip = N.ipv4_address h hlen;
    let f = tbs_find x C.oid_subject_alt_name buf blen;
    with d. assert (A.pts_to buf d);
    if (f.fd_ok && f.fd_some) {
      let nb = A.alloc 0uy PK.max_certificate_len;
      let san = Va.san_ok buf f.fd_len h hlen ip nb PK.max_certificate_len;
      A.free nb;
      if san {
        tbs_ku x 0x80uy buf blen
      } else {
        false
      }
    } else {
      false
    }
  }
}

(** {2 Certificates} *)

let epoch_eq () : Lemma (C.epoch_seconds == 62135596800) = assert_norm (C.epoch_seconds == 62135596800)

(** [valid_at y (t + epoch_seconds)], rejecting times past 2^64 - 1. *)
fn tbs_valid_at (x: t_TBSCertificate) (#pm: perm) (#y: Ghost.erased XP.tbs) (t: U64.t)
  requires tbs_rel pm x y
  returns r: bool
  ensures tbs_rel pm x y ** pure (r ==> C.valid_at y (U64.v t + C.epoch_seconds))
{
  epoch_eq ();
  if (U64.lte t 18446744011573954815UL) {
    let u = U64.add t 62135596800UL;
    assert (pure (U64.v u == U64.v t + C.epoch_seconds));
    let r = tbs_valid x u;
    rewrite each (U64.v u) as (U64.v t + C.epoch_seconds);
    r
  } else {
    false
  }
}

let body_ok (y: XP.tbs) (a: XP.alg_id) (t: nat) (leaf: bool) (hb: B.bytes) (issuer: bool) (below: nat) : GTot prop =
  C.is_v3 y /\ C.alg_same a (XP.tbs_sig_alg y) /\ C.valid_at y (t + C.epoch_seconds) /\
  C.extensions_ok (C.exts y) /\ C.ext_key_usage_ok (C.exts y) /\
  (leaf ==> C.subject_alt_name_ok (C.exts y) hb /\ C.key_usage_allows (C.exts y) 0x80uy) /\
  (issuer ==> bc_spec (C.exts y) below /\ C.key_usage_allows (C.exts y) 0x04uy)

fn cert_body (x: t_TBSCertificate) (#pm: perm) (#y: Ghost.erased XP.tbs)
  (a: t_AlgorithmIdentifier) (#pa: perm) (#va: Ghost.erased XP.alg_id)
  (t: U64.t) (leaf: bool) (h: A.array U8.t) (hlen: SZ.t) (#hb: Ghost.erased (Seq.seq U8.t))
  (issuer: bool) (below: U32.t)
  requires tbs_rel pm x y ** arel true d_AlgorithmIdentifier pa a va ** A.pts_to h hb ** pure (F.ok_len hb hlen)
  returns r: bool
  ensures tbs_rel pm x y ** arel true d_AlgorithmIdentifier pa a va ** A.pts_to h hb **
          pure (r ==> body_ok y va (U64.v t) leaf (F.cb hb hlen) issuer (U32.v below))
{
  let buf = A.alloc 0uy PK.max_certificate_len;
  let v3 = tbs_v3 x;
  let al = tbs_alg_same x a;
  let va_ = tbs_valid_at x t;
  let ex = tbs_exts_ok x;
  let ek = tbs_eku x buf PK.max_certificate_len;
  let lf = tbs_leaf x leaf h hlen buf PK.max_certificate_len;
  let is = tbs_issuer x issuer below buf PK.max_certificate_len;
  A.free buf;
  (v3 && al && va_ && ex && ek && lf && is)
}

(** The certificate [b[0, len)]. *)
let cert_at (b: Seq.seq U8.t) (len: SZ.t) : GTot (option XP.certificate) =
  C.parse_certificate (F.cb b len)

let cb_prefix (b: Seq.seq U8.t) (len: SZ.t)
: Lemma (requires SZ.v len <= Seq.length b) (ensures F.cb b len == Seq.slice b 0 (SZ.v len))
= assert (Seq.equal (F.cb b len) (Seq.slice b 0 (SZ.v len)))

let cert_ok_spec (o: option XP.certificate) (t: nat) (leaf: bool) (hb: B.bytes) (issuer: bool) (below: nat) : GTot prop =
  match o with
  | Some v -> C.path_ok v t /\ (leaf ==> C.leaf_ok v hb) /\ (issuer ==> C.issuer_ok v below)
  | None -> False

let body_cert (v: XP.certificate) (t: nat) (leaf: bool) (hb: B.bytes) (issuer: bool) (below: nat)
: Lemma (requires body_ok (XP.cert_tbs v) (XP.cert_sig_alg v) t leaf hb issuer below)
        (ensures cert_ok_spec (Some v) t leaf hb issuer below)
= ()

(** [path_ok] of the certificate [c[0, len)] at [t], with [leaf_ok] for the
    host [h[0, hlen)] if [leaf] and [issuer_ok] with [below] intermediates
    under it if [issuer]. *)
fn cert_check (c: A.array U8.t) (#p: perm) (#b: Ghost.erased (Seq.seq U8.t)) (len: SZ.t{SZ.v len <= Seq.length b})
  (t: U64.t) (leaf: bool) (h: A.array U8.t) (hlen: SZ.t) (#hb: Ghost.erased (Seq.seq U8.t))
  (issuer: bool) (below: U32.t)
  requires A.pts_to c #p b ** A.pts_to h hb ** pure (F.ok_len hb hlen)
  returns r: bool
  ensures A.pts_to c #p b ** A.pts_to h hb **
          pure (r ==> cert_ok_spec (cert_at b len) (U64.v t) leaf (F.cb hb hlen) issuer (U32.v below))
{
  cb_prefix b len;
  half_pos p;
  let s = prefix_slice c #p #b len;
  let o = open_whole validate_Certificate parse_Certificate s;
  match o {
    None -> {
      unfold (whole_res d_Certificate p s (Seq.slice b 0 (SZ.v len)) None);
      elim_trade (S.pts_to s #p (Seq.slice b 0 (SZ.v len))) (A.pts_to c #p b);
      false
    }
    Some x -> {
      unfold (whole_res d_Certificate p s (Seq.slice b 0 (SZ.v len)) (Some x));
      with v. assert (arel true d_Certificate p x v);
      cert_unpack ();
      unfold (cert_flat p x v);
      let r = cert_body x.tbsCertificate.value x.signatureAlgorithm t leaf h hlen issuer below;
      fold (cert_flat p x v);
      cert_pack ();
      elim_trade (arel true d_Certificate p x v) (S.pts_to s #p (Seq.slice b 0 (SZ.v len)));
      elim_trade (S.pts_to s #p (Seq.slice b 0 (SZ.v len))) (A.pts_to c #p b);
      if r {
        body_cert v (U64.v t) leaf (F.cb hb hlen) issuer (U32.v below);
        true
      } else {
        false
      }
    }
  }
}

(** {2 Issuer names} *)

fn tbs_names (xc: t_TBSCertificate) (#pc: perm) (#yc: Ghost.erased XP.tbs)
  (xp: t_TBSCertificate) (#pp: perm) (#yp: Ghost.erased XP.tbs)
  requires tbs_rel pc xc yc ** tbs_rel pp xp yp
  returns r: bool
  ensures tbs_rel pc xc yc ** tbs_rel pp xp yp **
          pure (r ==> Seq.eq (C.name_bytes (XP.tbs_issuer yc)) (C.name_bytes (XP.tbs_subject yp)))
{
  unfold (tbs_rel pc xc yc);
  unfold (tbs_rel pp xp yp);
  let r = name_same xc.issuer xp.subject;
  fold (tbs_rel pc xc yc);
  fold (tbs_rel pp xp yp);
  r
}

let names_spec (oc op: option XP.certificate) : GTot prop =
  match oc, op with
  | Some c, Some p -> C.names_issuer c p
  | _ -> False

fn names_body (xc: t_Certificate) (#pc: perm) (#vc: Ghost.erased XP.certificate)
  (xp: t_Certificate) (#pp: perm) (#vp: Ghost.erased XP.certificate)
  requires arel true d_Certificate pc xc vc ** arel true d_Certificate pp xp vp
  returns r: bool
  ensures arel true d_Certificate pc xc vc ** arel true d_Certificate pp xp vp **
          pure (r ==> C.names_issuer vc vp)
{
  half_pos pc;
  half_pos pp;
  cert_unpack #pc #xc #vc ();
  cert_unpack #pp #xp #vp ();
  unfold (cert_flat pc xc vc);
  unfold (cert_flat pp xp vp);
  let r = tbs_names xc.tbsCertificate.value xp.tbsCertificate.value;
  fold (cert_flat pc xc vc);
  fold (cert_flat pp xp vp);
  cert_pack #pc #xc #vc ();
  cert_pack #pp #xp #vp ();
  r
}

(** [names_issuer] of the certificates [c[0, clen)] and [d[0, dlen)]. *)
fn names_check (c: A.array U8.t) (#p: perm) (#b: Ghost.erased (Seq.seq U8.t)) (clen: SZ.t{SZ.v clen <= Seq.length b})
  (d: A.array U8.t) (#q: perm) (#e: Ghost.erased (Seq.seq U8.t)) (dlen: SZ.t{SZ.v dlen <= Seq.length e})
  requires A.pts_to c #p b ** A.pts_to d #q e
  returns r: bool
  ensures A.pts_to c #p b ** A.pts_to d #q e ** pure (r ==> names_spec (cert_at b clen) (cert_at e dlen))
{
  cb_prefix b clen;
  cb_prefix e dlen;
  let s = prefix_slice c #p #b clen;
  let o = open_whole validate_Certificate parse_Certificate s;
  match o {
    None -> {
      unfold (whole_res d_Certificate p s (Seq.slice b 0 (SZ.v clen)) None);
      elim_trade (S.pts_to s #p (Seq.slice b 0 (SZ.v clen))) (A.pts_to c #p b);
      false
    }
    Some x -> {
      unfold (whole_res d_Certificate p s (Seq.slice b 0 (SZ.v clen)) (Some x));
      with v. assert (arel true d_Certificate p x v);
      let t = prefix_slice d #q #e dlen;
      let o2 = open_whole validate_Certificate parse_Certificate t;
      match o2 {
        None -> {
          unfold (whole_res d_Certificate q t (Seq.slice e 0 (SZ.v dlen)) None);
          elim_trade (S.pts_to t #q (Seq.slice e 0 (SZ.v dlen))) (A.pts_to d #q e);
          elim_trade (arel true d_Certificate p x v) (S.pts_to s #p (Seq.slice b 0 (SZ.v clen)));
          elim_trade (S.pts_to s #p (Seq.slice b 0 (SZ.v clen))) (A.pts_to c #p b);
          false
        }
        Some y -> {
          unfold (whole_res d_Certificate q t (Seq.slice e 0 (SZ.v dlen)) (Some y));
          with w. assert (arel true d_Certificate q y w);
          let r = names_body x y;
          elim_trade (arel true d_Certificate q y w) (S.pts_to t #q (Seq.slice e 0 (SZ.v dlen)));
          elim_trade (S.pts_to t #q (Seq.slice e 0 (SZ.v dlen))) (A.pts_to d #q e);
          elim_trade (arel true d_Certificate p x v) (S.pts_to s #p (Seq.slice b 0 (SZ.v clen)));
          elim_trade (S.pts_to s #p (Seq.slice b 0 (SZ.v clen))) (A.pts_to c #p b);
          r
        }
      }
    }
  }
}

(** {2 Signatures} *)

inline_for_extraction noextract
let eq_sha256_rsa_oid : eq_from_t C.sha256_rsa_oid =
  norm [delta_only [`%mk_eq; `%C.sha256_rsa_oid]; zeta; iota; primops] (mk_eq C.sha256_rsa_oid)

fn lit_sha256_rsa_oid (s: S.slice U8.t) (#pm: perm) (#w: Ghost.erased (Seq.seq U8.t))
  requires S.pts_to s #pm w
  returns r: bool
  ensures S.pts_to s #pm w ** pure (r <==> KS.bytes_is w C.sha256_rsa_oid)
{
  S.pts_to_len s;
  let r = eq_sha256_rsa_oid s 0sz #pm #w;
  assert (pure (Seq.slice w 0 (Seq.length w) `Seq.equal` w));
  r
}

inline_for_extraction noextract
let eq_sha384_rsa_oid : eq_from_t C.sha384_rsa_oid =
  norm [delta_only [`%mk_eq; `%C.sha384_rsa_oid]; zeta; iota; primops] (mk_eq C.sha384_rsa_oid)

fn lit_sha384_rsa_oid (s: S.slice U8.t) (#pm: perm) (#w: Ghost.erased (Seq.seq U8.t))
  requires S.pts_to s #pm w
  returns r: bool
  ensures S.pts_to s #pm w ** pure (r <==> KS.bytes_is w C.sha384_rsa_oid)
{
  S.pts_to_len s;
  let r = eq_sha384_rsa_oid s 0sz #pm #w;
  assert (pure (Seq.slice w 0 (Seq.length w) `Seq.equal` w));
  r
}

inline_for_extraction noextract
let eq_sha512_rsa_oid : eq_from_t C.sha512_rsa_oid =
  norm [delta_only [`%mk_eq; `%C.sha512_rsa_oid]; zeta; iota; primops] (mk_eq C.sha512_rsa_oid)

fn lit_sha512_rsa_oid (s: S.slice U8.t) (#pm: perm) (#w: Ghost.erased (Seq.seq U8.t))
  requires S.pts_to s #pm w
  returns r: bool
  ensures S.pts_to s #pm w ** pure (r <==> KS.bytes_is w C.sha512_rsa_oid)
{
  S.pts_to_len s;
  let r = eq_sha512_rsa_oid s 0sz #pm #w;
  assert (pure (Seq.slice w 0 (Seq.length w) `Seq.equal` w));
  r
}

inline_for_extraction noextract
let eq_ecdsa_sha256_oid : eq_from_t C.ecdsa_sha256_oid =
  norm [delta_only [`%mk_eq; `%C.ecdsa_sha256_oid]; zeta; iota; primops] (mk_eq C.ecdsa_sha256_oid)

fn lit_ecdsa_sha256_oid (s: S.slice U8.t) (#pm: perm) (#w: Ghost.erased (Seq.seq U8.t))
  requires S.pts_to s #pm w
  returns r: bool
  ensures S.pts_to s #pm w ** pure (r <==> KS.bytes_is w C.ecdsa_sha256_oid)
{
  S.pts_to_len s;
  let r = eq_ecdsa_sha256_oid s 0sz #pm #w;
  assert (pure (Seq.slice w 0 (Seq.length w) `Seq.equal` w));
  r
}

inline_for_extraction noextract
let eq_ecdsa_sha384_oid : eq_from_t C.ecdsa_sha384_oid =
  norm [delta_only [`%mk_eq; `%C.ecdsa_sha384_oid]; zeta; iota; primops] (mk_eq C.ecdsa_sha384_oid)

fn lit_ecdsa_sha384_oid (s: S.slice U8.t) (#pm: perm) (#w: Ghost.erased (Seq.seq U8.t))
  requires S.pts_to s #pm w
  returns r: bool
  ensures S.pts_to s #pm w ** pure (r <==> KS.bytes_is w C.ecdsa_sha384_oid)
{
  S.pts_to_len s;
  let r = eq_ecdsa_sha384_oid s 0sz #pm #w;
  assert (pure (Seq.slice w 0 (Seq.length w) `Seq.equal` w));
  r
}

fn params_none (x: t_AlgorithmIdentifier_parameters_opt) (#pm: perm) (#y: Ghost.erased (option asn1_value))
  requires prel_option any_rel pm (oview_AlgorithmIdentifier_parameters x) y
  returns r: bool
  ensures prel_option any_rel pm (oview_AlgorithmIdentifier_parameters x) y ** pure (r <==> None? y)
{
  match x {
    AlgorithmIdentifier_parameters_absent -> {
      rewrite (prel_option any_rel pm (oview_AlgorithmIdentifier_parameters x) y)
           as (prel_option any_rel pm None y);
      opt_none_elim any_rel pm y;
      rewrite (prel_option any_rel pm None y)
           as (prel_option any_rel pm (oview_AlgorithmIdentifier_parameters x) y);
      true
    }
    AlgorithmIdentifier_parameters_present ps -> {
      rewrite (prel_option any_rel pm (oview_AlgorithmIdentifier_parameters x) y)
           as (prel_option any_rel pm (Some ps) y);
      let b = opt_some_elim any_rel pm ps y;
      opt_some_intro any_rel pm ps b y;
      rewrite (prel_option any_rel pm (Some ps) y)
           as (prel_option any_rel pm (oview_AlgorithmIdentifier_parameters x) y);
      false
    }
  }
}

(* An AlgorithmIdentifier with OID [lo] and no parameters. *)
inline_for_extraction noextract
fn alg_none (lo: Ghost.erased (list U8.t)) (fo: lit_t lo)
  (a: t_AlgorithmIdentifier) (#pm: perm) (#v: Ghost.erased (asn1_t X.k_AlgorithmIdentifier))
  requires arel true d_AlgorithmIdentifier pm a v
  returns r: bool
  ensures arel true d_AlgorithmIdentifier pm a v **
          pure (r <==> (KS.oid_is (XP.alg_oid v) lo /\ None? (XP.alg_params v)))
{
  alg_eq pm a v;
  rewrite (arel true d_AlgorithmIdentifier pm a v) as (alg_rel pm a v);
  unfold alg_rel;
  unfold oid_rel;
  let ro = ser_is (E.leaf_enc ASN1_OID) lo fo a.algorithm;
  fold (oid_rel pm a.algorithm (fst v));
  let rp = params_none a.parameters;
  fold (alg_rel pm a v);
  rewrite (alg_rel pm a v) as (arel true d_AlgorithmIdentifier pm a v);
  (ro && rp)
}

(** Which branch of [signed_by] the signature algorithm takes: 1-3 for
    RSA PKCS #1 with SHA-256/384/512, 4-5 for ECDSA with SHA-256/384, 0 for
    none. *)
let alg_code (a: XP.alg_id) : GTot U8.t =
  if C.rsa_alg a C.sha256_rsa_oid then 1uy
  else if C.rsa_alg a C.sha384_rsa_oid then 2uy
  else if C.rsa_alg a C.sha512_rsa_oid then 3uy
  else if C.ecdsa_alg a C.ecdsa_sha256_oid then 4uy
  else if C.ecdsa_alg a C.ecdsa_sha384_oid then 5uy
  else 0uy

fn sig_alg_code (a: t_AlgorithmIdentifier) (#pm: perm) (#v: Ghost.erased XP.alg_id)
  requires arel true d_AlgorithmIdentifier pm a v
  returns r: U8.t
  ensures arel true d_AlgorithmIdentifier pm a v ** pure (r == alg_code v)
{
  let r1 = alg_is C.sha256_rsa_oid lit_sha256_rsa_oid KS.der_null K.lit_der_null a;
  let r2 = alg_is C.sha384_rsa_oid lit_sha384_rsa_oid KS.der_null K.lit_der_null a;
  let r3 = alg_is C.sha512_rsa_oid lit_sha512_rsa_oid KS.der_null K.lit_der_null a;
  let e4 = alg_none C.ecdsa_sha256_oid lit_ecdsa_sha256_oid a;
  let e5 = alg_none C.ecdsa_sha384_oid lit_ecdsa_sha384_oid a;
  if r1 { 1uy } else if r2 { 2uy } else if r3 { 3uy } else if e4 { 4uy } else if e5 { 5uy } else { 0uy }
}

(** The certificate's [TBSCertificate] bytes, copied into the front of [tv];
    0 if they do not fit. *)
fn tbs_copy (k: t_TBSCertificate_kept) (#pm: perm) (#y: Ghost.erased XP.tbs)
  (tv: A.array U8.t) (tlen: SZ.t) (#old: Ghost.erased (Seq.seq U8.t))
  requires keep_rel X.k_TBSCertificate pm (kview_TBSCertificate k).kraw y **
           A.pts_to tv old ** pure (scratch old tv tlen)
  returns n: SZ.t
  ensures keep_rel X.k_TBSCertificate pm (kview_TBSCertificate k).kraw y **
          (exists* d. A.pts_to tv d ** pure (scratch d tv tlen /\
            (SZ.v n > 0 ==> SZ.v n <= Seq.length d /\ Seq.slice d 0 (SZ.v n) == Ser.asn1_enc X.k_TBSCertificate y)))
{
  match k.raw {
    TBSCertificate_raw_absent -> {
      0sz
    }
    TBSCertificate_raw_present s -> {
      rewrite (keep_rel X.k_TBSCertificate pm (kview_TBSCertificate k).kraw y)
           as (keep_rel X.k_TBSCertificate pm (Some s) y);
      unfold (keep_rel X.k_TBSCertificate pm (Some s) y);
      unfold (prel_slice_ser (Ser.asn1_enc X.k_TBSCertificate) pm s y);
      let n = copy_slice s tv tlen;
      fold (prel_slice_ser (Ser.asn1_enc X.k_TBSCertificate) pm s y);
      fold (keep_rel X.k_TBSCertificate pm (Some s) y);
      rewrite (keep_rel X.k_TBSCertificate pm (Some s) y)
           as (keep_rel X.k_TBSCertificate pm (kview_TBSCertificate k).kraw y);
      n
    }
  }
}

(** The signature bytes, copied into the front of [sv]; 0 if they do not
    fit or have unused bits. *)
fn sig_copy (x: asn1_bitstring_impl) (#pm: perm) (#y: Ghost.erased asn1_bitstring_t)
  (sv: A.array U8.t) (slen: SZ.t) (#old: Ghost.erased (Seq.seq U8.t))
  requires asn1_bitstring_rel pm x y ** A.pts_to sv old ** pure (scratch old sv slen)
  returns n: SZ.t
  ensures asn1_bitstring_rel pm x y **
          (exists* d. A.pts_to sv d ** pure (scratch d sv slen /\
            (SZ.v n > 0 ==> BYTES_WITH_UNUSEDBITS?.unused y == 0uy /\
              SZ.v n <= Seq.length d /\ Seq.slice d 0 (SZ.v n) == BYTES_WITH_UNUSEDBITS?.b y)))
{
  unfold (asn1_bitstring_rel pm x y);
  if (x.unused = 0uy) {
    let n = copy_slice x.bytes sv slen;
    fold (asn1_bitstring_rel pm x y);
    n
  } else {
    fold (asn1_bitstring_rel pm x y);
    0sz
  }
}

type sig_info = { si_alg: U8.t; si_tn: SZ.t; si_sn: SZ.t }

inline_for_extraction noextract
let no_sig : sig_info = { si_alg = 0uy; si_tn = 0sz; si_sn = 0sz }

let sig_ok (o: option XP.certificate) (r: sig_info) (tb sb: Seq.seq U8.t) : prop =
  r.si_alg <> 0uy ==>
  (match o with
   | Some v ->
     r.si_alg == alg_code (XP.cert_sig_alg v) /\
     BYTES_WITH_UNUSEDBITS?.unused (XP.cert_sig v) == 0uy /\
     SZ.v r.si_tn <= Seq.length tb /\ SZ.v r.si_sn <= Seq.length sb /\
     CL.raw_slice tb 0 (SZ.v r.si_tn) == C.tbs_bytes v /\
     CL.raw_slice sb 0 (SZ.v r.si_sn) == BYTES_WITH_UNUSEDBITS?.b (XP.cert_sig v)
   | None -> False)

fn sig_body (x: t_Certificate) (#p: perm) (#v: Ghost.erased XP.certificate)
  (tv: A.array U8.t) (#t0: Ghost.erased (Seq.seq U8.t)) (sv: A.array U8.t) (#s0: Ghost.erased (Seq.seq U8.t))
  requires arel true d_Certificate p x v ** A.pts_to tv t0 ** A.pts_to sv s0 **
           pure (scratch t0 tv PK.max_certificate_len /\ scratch s0 sv PK.max_certificate_len)
  returns r: sig_info
  ensures arel true d_Certificate p x v ** (exists* tb sb. A.pts_to tv tb ** A.pts_to sv sb **
          pure (scratch tb tv PK.max_certificate_len /\ scratch sb sv PK.max_certificate_len /\
                sig_ok (Some (reveal v)) r tb sb))
{
  half_pos p;
  cert_unpack #p #x #v ();
  unfold (cert_flat p x v);
  let code = sig_alg_code x.signatureAlgorithm;
  let tn = tbs_copy x.tbsCertificate tv PK.max_certificate_len;
  let sn = sig_copy x.signatureValue sv PK.max_certificate_len;
  fold (cert_flat p x v);
  cert_pack #p #x #v ();
  if (code = 0uy || tn = 0sz || sn = 0sz) {
    no_sig
  } else {
    Mksig_info code tn sn
  }
}

(** The signature parts of the certificate [c[0, clen)]: its algorithm, its
    [TBSCertificate] bytes (into [tv]) and its signature (into [sv]). *)
fn sig_parts (c: A.array U8.t) (#p: perm) (#b: Ghost.erased (Seq.seq U8.t)) (clen: SZ.t{SZ.v clen <= Seq.length b})
  (tv: A.array U8.t) (#t0: Ghost.erased (Seq.seq U8.t)) (sv: A.array U8.t) (#s0: Ghost.erased (Seq.seq U8.t))
  requires A.pts_to c #p b ** A.pts_to tv t0 ** A.pts_to sv s0 **
           pure (scratch t0 tv PK.max_certificate_len /\ scratch s0 sv PK.max_certificate_len)
  returns r: sig_info
  ensures A.pts_to c #p b ** (exists* tb sb. A.pts_to tv tb ** A.pts_to sv sb **
          pure (scratch tb tv PK.max_certificate_len /\ scratch sb sv PK.max_certificate_len /\
                sig_ok (cert_at b clen) r tb sb))
{
  cb_prefix b clen;
  let s = prefix_slice c #p #b clen;
  let o = open_whole validate_Certificate parse_Certificate s;
  match o {
    None -> {
      unfold (whole_res d_Certificate p s (Seq.slice b 0 (SZ.v clen)) None);
      elim_trade (S.pts_to s #p (Seq.slice b 0 (SZ.v clen))) (A.pts_to c #p b);
      no_sig
    }
    Some x -> {
      unfold (whole_res d_Certificate p s (Seq.slice b 0 (SZ.v clen)) (Some x));
      with v. assert (arel true d_Certificate p x v);
      let r = sig_body x tv sv;
      elim_trade (arel true d_Certificate p x v) (S.pts_to s #p (Seq.slice b 0 (SZ.v clen)));
      elim_trade (S.pts_to s #p (Seq.slice b 0 (SZ.v clen))) (A.pts_to c #p b);
      r
    }
  }
}

let verify_spec (kind code: U8.t) (k e tbs s: B.bytes) : GTot bool =
  if kind = 1uy then
    (if code = 1uy then CS.rsa_pkcs1_verify CS.Pkcs1Sha256 k e tbs s
     else if code = 2uy then CS.rsa_pkcs1_verify CS.Pkcs1Sha384 k e tbs s
     else if code = 3uy then CS.rsa_pkcs1_verify CS.Pkcs1Sha512 k e tbs s
     else false)
  else if kind = 2uy then
    (if code = 4uy then Cr.p256_verify false k tbs s
     else if code = 5uy then Cr.p256_verify true k tbs s
     else false)
  else if kind = 3uy then
    (if code = 4uy then Cr.p384_verify false k tbs s
     else if code = 5uy then Cr.p384_verify true k tbs s
     else false)
  else false

fn verify_sig (kind code: U8.t)
  (kv: A.array U8.t) (kl: SZ.t) (ev: A.array U8.t) (el: SZ.t)
  (tv: A.array U8.t) (tn: SZ.t) (sv: A.array U8.t) (sn: SZ.t)
  requires A.pts_to kv 'kb ** A.pts_to ev 'eb ** A.pts_to tv 'tb ** A.pts_to sv 'sb **
           pure (SZ.v kl <= Seq.length 'kb /\ SZ.v el <= Seq.length 'eb /\
                 SZ.v tn <= Seq.length 'tb /\ SZ.v sn <= Seq.length 'sb)
  returns r: bool
  ensures A.pts_to kv 'kb ** A.pts_to ev 'eb ** A.pts_to tv 'tb ** A.pts_to sv 'sb **
          pure (r ==> verify_spec kind code (CL.raw_slice 'kb 0 (SZ.v kl)) (CL.raw_slice 'eb 0 (SZ.v el))
                        (CL.raw_slice 'tb 0 (SZ.v tn)) (CL.raw_slice 'sb 0 (SZ.v sn)))
{
  if (kind = 1uy && (code = 1uy || code = 2uy || code = 3uy)) {
    let h = (if code = 1uy then CS.Pkcs1Sha256 else if code = 2uy then CS.Pkcs1Sha384 else CS.Pkcs1Sha512);
    Cr.verify_rsa_pkcs1 h kv kl ev el tv tn sv sn
  } else if (kind = 2uy && (code = 4uy || code = 5uy)) {
    Cr.verify_ecdsa_secp256r1 (code = 5uy) kv kl tv tn sv sn
  } else if (kind = 3uy && (code = 4uy || code = 5uy)) {
    Cr.verify_ecdsa_secp384r1 (code = 5uy) kv kl tv tn sv sn
  } else {
    false
  }
}

let signed_spec (o: option XP.certificate) (ib: B.bytes) : GTot prop =
  match o with
  | Some v -> C.signed_by v ib
  | None -> False

#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
let signed_intro (o: option XP.certificate) (ib: B.bytes) (kind: U8.t) (r: sig_info) (tb sb k e: B.bytes)
: Lemma (requires r.si_alg <> 0uy /\ sig_ok o r tb sb /\
                  (kind == 1uy ==> CS.certificate_raw_public_key ib == Some (CS.RawRsa k e)) /\
                  (kind == 2uy ==> CS.certificate_raw_public_key ib == Some (CS.RawP256 k)) /\
                  (kind == 3uy ==> CS.certificate_raw_public_key ib == Some (CS.RawP384 k)) /\
                  verify_spec kind r.si_alg k e (CL.raw_slice tb 0 (SZ.v r.si_tn)) (CL.raw_slice sb 0 (SZ.v r.si_sn)))
        (ensures signed_spec o ib)
= let Some v = o in
  let a = XP.cert_sig_alg v in
  let tbs = C.tbs_bytes v in
  let s = BYTES_WITH_UNUSEDBITS?.b (XP.cert_sig v) in
  let code = r.si_alg in
  assert (code == alg_code a);
  assert (verify_spec kind code k e tbs s);
  if kind = 1uy then begin
    assert (CS.certificate_raw_public_key ib == Some (CS.RawRsa k e));
    if code = 1uy then assert (C.rsa_alg a C.sha256_rsa_oid)
    else if code = 2uy then assert (not (C.rsa_alg a C.sha256_rsa_oid) /\ C.rsa_alg a C.sha384_rsa_oid)
    else assert (not (C.rsa_alg a C.sha256_rsa_oid) /\ not (C.rsa_alg a C.sha384_rsa_oid) /\ C.rsa_alg a C.sha512_rsa_oid)
  end else if kind = 2uy then begin
    assert (CS.certificate_raw_public_key ib == Some (CS.RawP256 k));
    if code = 4uy then assert (C.ecdsa_alg a C.ecdsa_sha256_oid)
    else assert (not (C.ecdsa_alg a C.ecdsa_sha256_oid) /\ C.ecdsa_alg a C.ecdsa_sha384_oid)
  end else begin
    assert (CS.certificate_raw_public_key ib == Some (CS.RawP384 k));
    if code = 4uy then assert (C.ecdsa_alg a C.ecdsa_sha256_oid)
    else assert (not (C.ecdsa_alg a C.ecdsa_sha256_oid) /\ C.ecdsa_alg a C.ecdsa_sha384_oid)
  end
#pop-options

inline_for_extraction noextract
let key_cap : SZ.t = 1024sz

(** [signed_by] of the certificate [c[0, clen)] under the key of the
    certificate [d[0, dlen)]. *)
fn signed_check (c: A.array U8.t) (#p: perm) (#b: Ghost.erased (Seq.seq U8.t)) (clen: SZ.t{SZ.v clen <= Seq.length b})
  (d: A.array U8.t) (#e: Ghost.erased (Seq.seq U8.t)) (dlen: SZ.t{SZ.v dlen <= Seq.length e})
  requires A.pts_to c #p b ** A.pts_to d e
  returns r: bool
  ensures A.pts_to c #p b ** A.pts_to d e ** pure (r ==> signed_spec (cert_at b clen) (F.cb e dlen))
{
  let tv = A.alloc 0uy PK.max_certificate_len;
  let sv = A.alloc 0uy PK.max_certificate_len;
  let si = sig_parts c clen tv sv;
  with tb sb. assert (A.pts_to tv tb ** A.pts_to sv sb);
  if (si.si_alg = 0uy) {
    A.free tv;
    A.free sv;
    false
  } else {
    let kv = A.alloc 0uy key_cap;
    let ev = A.alloc 0uy key_cap;
    let lv = A.alloc 0sz 2sz;
    let kind = K.certificate_raw_public_key d dlen kv key_cap ev key_cap lv;
    with kb eb ls. assert (A.pts_to kv kb ** A.pts_to ev eb ** A.pts_to lv ls);
    let kl = lv.(0sz);
    let el = lv.(1sz);
    let ok = verify_sig kind si.si_alg kv kl ev el tv si.si_tn sv si.si_sn;
    A.free kv;
    A.free ev;
    A.free lv;
    A.free tv;
    A.free sv;
    if ok {
      signed_intro (cert_at b clen) (F.cb e dlen) kind si tb sb
        (CL.raw_slice kb 0 (SZ.v kl)) (CL.raw_slice eb 0 (SZ.v el));
      true
    } else {
      false
    }
  }
}
