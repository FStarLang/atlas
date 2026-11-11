module TLS13.Impl.X509.ASN1

(** Support for reading certificates with the parsers everparse-asn1
    generates from [src/asn1/X509.asn] ([TLS13.Wire.Generated.X509.Impl]).

    A parsed value [x] is related to its ASN.1 value [v] by
    [arel true d_T pm x v], computed from the type's descriptor.  The lemmas
    here unfold that relation one level for the types the TLS code inspects
    into a separating conjunction of named field relations (with the
    sub-fields' own [arel] folded), so that a field can be borrowed and given
    back with [rewrite]; and the comparators test a field's bytes against a
    constant. *)

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Trade
open ASN1.Base
open ASN1.Pulse.Rel
open ASN1.Spec.Value.Enc
open TLS13.Wire.Generated.X509.Impl

module A = Pulse.Lib.Array
module AP = Pulse.Lib.ArrayPtr
module C = TLS13.Crypto.Spec
module KS = TLS13.X509.KeySpec
module E = ASN1.Spec.Content.Enc
module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module VE = ASN1.Spec.Value.Enc
module X = TLS13.Wire.Generated.X509
module XP = TLS13.X509.Profile

(** {2 Literal comparison} *)

let lit_at (w: Seq.seq U8.t) (i: nat) (l: list U8.t) : prop =
  i <= Seq.length w /\ Seq.slice w i (Seq.length w) == Seq.seq_of_list l

inline_for_extraction noextract
let eq_from_t (l: list U8.t) =
  (s: S.slice U8.t) -> (i: SZ.t) -> (#pm: perm) -> (#w: Ghost.erased (Seq.seq U8.t)) ->
  stt bool (S.pts_to s #pm w ** pure (SZ.v i <= Seq.length w))
    (fun r -> S.pts_to s #pm w ** pure (r <==> lit_at w (SZ.v i) l))

let lit_at_nil (w: Seq.seq U8.t) (i: nat{i <= Seq.length w})
: Lemma (lit_at w i [] <==> i == Seq.length w)
= Seq.lemma_seq_of_list_induction #U8.t [];
  if i = Seq.length w then Seq.lemma_eq_elim (Seq.slice w i (Seq.length w)) (Seq.seq_of_list #U8.t [])

let lit_at_cons (w: Seq.seq U8.t) (i: nat{i < Seq.length w}) (h: U8.t) (tl: list U8.t)
: Lemma (lit_at w i (h :: tl) <==> (Seq.index w i == h /\ lit_at w (i + 1) tl))
= Seq.lemma_seq_of_list_induction (h :: tl);
  let a = Seq.slice w i (Seq.length w) in
  let b = Seq.slice w (i + 1) (Seq.length w) in
  Seq.cons_head_tail a;
  assert (Seq.equal (Seq.tail a) b);
  Classical.move_requires (Seq.lemma_cons_inj (Seq.head a) h b) (Seq.seq_of_list tl)

let lit_at_end (w: Seq.seq U8.t) (h: U8.t) (tl: list U8.t)
: Lemma (~ (lit_at w (Seq.length w) (h :: tl)))
= Seq.lemma_seq_of_list_induction (h :: tl)

inline_for_extraction noextract
fn eq_nil () : eq_from_t [] =
  (s: S.slice U8.t) (i: SZ.t) (#pm: perm) (#w: Ghost.erased (Seq.seq U8.t))
{
  S.pts_to_len s;
  lit_at_nil w (SZ.v i);
  (i = S.len s)
}

inline_for_extraction noextract
fn eq_cons (h: U8.t) (tl: Ghost.erased (list U8.t)) (f: eq_from_t tl) : eq_from_t (h :: tl) =
  (s: S.slice U8.t) (i: SZ.t) (#pm: perm) (#w: Ghost.erased (Seq.seq U8.t))
{
  S.pts_to_len s;
  if (i = S.len s) {
    lit_at_end w h tl;
    false
  } else {
    lit_at_cons w (SZ.v i) h tl;
    let b = S.(s.(i));
    if (b = h) { f s (SZ.add i 1sz) #pm #w } else { false }
  }
}

(** The comparator for a constant [l], unrolled by
    [norm [delta_only [`%mk_eq; `%l]; zeta; iota; primops] (mk_eq l)] in an
    [inline_for_extraction noextract let].  Wrap it in a [fn] of type [lit_t l]
    before passing it to [ser_is] and friends: Custard mis-types a comparator
    lambda applied through a parameter. *)
inline_for_extraction noextract
let rec mk_eq (l: list U8.t) : eq_from_t l =
  match l with
  | [] -> eq_nil ()
  | h :: tl -> (fun s i #pm #w -> eq_cons h tl (mk_eq tl) s i #pm #w)

(** {2 Field relations} *)

let oid_rel (pm: perm) (s: S.slice U8.t) (o: asn1_oid_t) : slprop = prel_slice_ser (E.leaf_enc ASN1_OID) pm s o
let any_rel (pm: perm) (s: S.slice U8.t) (v: asn1_value) : slprop = prel_slice_ser asn1_value_enc pm s v

let alg_rel (pm: perm) (x: t_AlgorithmIdentifier) (y: asn1_t X.k_AlgorithmIdentifier) : slprop =
  oid_rel pm x.algorithm (fst y) ** prel_option any_rel pm (oview_AlgorithmIdentifier_parameters x.parameters) (snd y)

let tac (l: list string) : FStar.Tactics.Tac unit =
  FStar.Tactics.norm [delta_only (l @ [`%arel; `%crel; `%irel; `%drel; `%asn1_terminal_rel; `%coerce_eq; `%prel_pair; `%prel_option;
     `%oid_rel; `%any_rel; `%alg_rel]); zeta; iota; primops];
  FStar.Tactics.trefl ()

let alg_eq (pm: perm) (x: t_AlgorithmIdentifier) (y: asn1_t X.k_AlgorithmIdentifier)
: Lemma (arel true d_AlgorithmIdentifier pm x y == alg_rel pm x y)
= assert (arel true d_AlgorithmIdentifier pm x y == alg_rel pm x y)
    by (tac [`%d_AlgorithmIdentifier; `%cd_AlgorithmIdentifier; `%view_AlgorithmIdentifier])

let spki_rel (pm: perm) (x: t_SubjectPublicKeyInfo) (y: asn1_t X.k_SubjectPublicKeyInfo) : slprop =
  arel true d_AlgorithmIdentifier pm x.algorithm (fst y) ** asn1_bitstring_rel pm x.subjectPublicKey (snd y)

let spki_eq (pm: perm) (x: t_SubjectPublicKeyInfo) (y: asn1_t X.k_SubjectPublicKeyInfo)
: Lemma (arel true d_SubjectPublicKeyInfo pm x y == spki_rel pm x y)
= assert (arel true d_SubjectPublicKeyInfo pm x y == spki_rel pm x y)
    by (tac [`%d_SubjectPublicKeyInfo; `%cd_SubjectPublicKeyInfo; `%view_SubjectPublicKeyInfo; `%spki_rel])

let rsa_rel (pm: perm) (x: t_RSAPublicKey) (y: asn1_t X.k_RSAPublicKey) : slprop =
  asn1_int_rel asn1_any_integer_bound pm x.modulus (fst y) ** asn1_int_rel asn1_any_integer_bound pm x.publicExponent (snd y)

let rsa_eq (pm: perm) (x: t_RSAPublicKey) (y: asn1_t X.k_RSAPublicKey)
: Lemma (arel true d_RSAPublicKey pm x y == rsa_rel pm x y)
= assert (arel true d_RSAPublicKey pm x y == rsa_rel pm x y)
    by (tac [`%d_RSAPublicKey; `%cd_RSAPublicKey; `%view_RSAPublicKey; `%rsa_rel])

let cert_rel (pm: perm) (x: t_Certificate) (y: asn1_t X.k_Certificate) : slprop =
  arel true d_TBSCertificate pm x.tbsCertificate (fst y) **
  (arel true d_AlgorithmIdentifier pm x.signatureAlgorithm (fst (snd y)) **
   asn1_bitstring_rel pm x.signatureValue (snd (snd y)))

let cert_eq (pm: perm) (x: t_Certificate) (y: asn1_t X.k_Certificate)
: Lemma (arel true d_Certificate pm x y == cert_rel pm x y)
= assert (arel true d_Certificate pm x y == cert_rel pm x y)
    by (tac [`%d_Certificate; `%cd_Certificate; `%view_Certificate; `%cert_rel])

let tbs_kept_rel (pm: perm) (x: t_TBSCertificate_kept) (y: asn1_t X.k_TBSCertificate) : slprop =
  arel true dbase_TBSCertificate (pm /. 2.0R) x.value y **
  keep_rel X.k_TBSCertificate (pm /. 2.0R) (kview_TBSCertificate x).kraw y **
  pure (Some? (kview_TBSCertificate x).kraw)

let tbs_kept_eq (pm: perm) (x: t_TBSCertificate_kept) (y: asn1_t X.k_TBSCertificate)
: Lemma (arel true d_TBSCertificate pm x y == tbs_kept_rel pm x y)
= assert (arel true d_TBSCertificate pm x y == tbs_kept_rel pm x y)
    by (FStar.Tactics.norm [delta_only [`%arel; `%d_TBSCertificate; `%tbs_kept_rel]; zeta; iota; primops];
        FStar.Tactics.trefl ())

let ver_rel (pm: perm) (x: t_TBSCertificate_version_opt) (y: asn1_decorated_t_core (ASN1_DEFAULT_TERMINAL (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 0) #(ASN1_PREFIXED_TERMINAL (ASN1.Syntax.mk_constant_id 2) (ASN1_INTEGER asn1_any_integer_bound)) X.dv_TBSCertificate_version)) : slprop =
  drel true (DD_VIEW (DD_DEFAULT (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 0) #(ASN1_PREFIXED_TERMINAL (ASN1.Syntax.mk_constant_id 2) (ASN1_INTEGER asn1_any_integer_bound)) X.dv_TBSCertificate_version) t_TBSCertificate_version_opt oview_TBSCertificate_version omk_TBSCertificate_version ()) pm x y

let arel_ilc (kb: bool) (id: asn1_id_t) (#c: asn1_content_k) (#t: Type0) (cd: cdesc c t) (pm: perm) (x: t) (y: asn1_content_t c)
: Lemma (arel kb (D_ILC id cd) pm x y == crel kb cd pm x y)
= assert (arel kb (D_ILC id cd) pm x y == crel kb cd pm x y) by (FStar.Tactics.norm [delta_only [`%arel]; zeta; iota]; FStar.Tactics.trefl ())

let tbs_rel (pm: perm) (x: t_TBSCertificate) (y: asn1_t X.k_TBSCertificate) : slprop =
  ver_rel pm x.version (fst y) **
  (arel true d_CertificateSerialNumber pm x.serialNumber (fst (snd y)) **
  (arel true d_AlgorithmIdentifier pm x.signature (fst (snd (snd y))) **
  (arel true d_Name pm x.issuer (fst (snd (snd (snd y)))) **
  (arel true d_Validity pm x.validity (fst (snd (snd (snd (snd y))))) **
  (arel true d_Name pm x.subject (fst (snd (snd (snd (snd (snd y)))))) **
  (arel true d_SubjectPublicKeyInfo pm x.subjectPublicKeyInfo (fst (snd (snd (snd (snd (snd (snd y))))))) **
  (prel_option (arel true (D_ILC (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC PRIMITIVE 1) cd_UniqueIdentifier)) pm (oview_TBSCertificate_issuerUniqueID x.issuerUniqueID) (fst (snd (snd (snd (snd (snd (snd (snd y)))))))) **
  (prel_option (arel true (D_ILC (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC PRIMITIVE 2) cd_UniqueIdentifier)) pm (oview_TBSCertificate_subjectUniqueID x.subjectUniqueID) (fst (snd (snd (snd (snd (snd (snd (snd (snd y))))))))) **
   prel_option (arel true (D_ILC (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 3) (CD_PREFIXED d_Extensions))) pm (oview_TBSCertificate_extensions x.extensions) (snd (snd (snd (snd (snd (snd (snd (snd (snd y)))))))))))))))))

let tbs_eq (pm: perm) (x: t_TBSCertificate) (y: asn1_t X.k_TBSCertificate)
: Lemma (arel true dbase_TBSCertificate pm x y == tbs_rel pm x y)
= arel_ilc true X.id_TBSCertificate cd_TBSCertificate pm x y;
  assert (crel true cd_TBSCertificate pm x y == tbs_rel pm x y)
    by (FStar.Tactics.norm [delta_only [`%crel; `%irel; `%drel; `%cd_TBSCertificate; `%view_TBSCertificate; `%tbs_rel; `%ver_rel; `%prel_option]; zeta; iota; primops];
        FStar.Tactics.trefl ())

let cert_flat (pm: perm) (x: t_Certificate) (v: asn1_t X.k_Certificate) : slprop =
  tbs_rel (pm /. 2.0R) x.tbsCertificate.value (fst v) **
  keep_rel X.k_TBSCertificate (pm /. 2.0R) (kview_TBSCertificate x.tbsCertificate).kraw (fst v) **
  pure (Some? (kview_TBSCertificate x.tbsCertificate).kraw) **
  arel true d_AlgorithmIdentifier pm x.signatureAlgorithm (fst (snd v)) **
  asn1_bitstring_rel pm x.signatureValue (snd (snd v))

ghost
fn cert_unpack (#pm: perm) (#x: t_Certificate) (#v: asn1_t X.k_Certificate) ()
  requires arel true d_Certificate pm x v
  ensures cert_flat pm x v
{
  cert_eq pm x v;
  rewrite (arel true d_Certificate pm x v) as (cert_rel pm x v);
  unfold cert_rel;
  tbs_kept_eq pm x.tbsCertificate (fst v);
  rewrite (arel true d_TBSCertificate pm x.tbsCertificate (fst v)) as (tbs_kept_rel pm x.tbsCertificate (fst v));
  unfold tbs_kept_rel;
  tbs_eq (pm /. 2.0R) x.tbsCertificate.value (fst v);
  rewrite (arel true dbase_TBSCertificate (pm /. 2.0R) x.tbsCertificate.value (fst v)) as (tbs_rel (pm /. 2.0R) x.tbsCertificate.value (fst v));
  fold (cert_flat pm x v)
}

ghost
fn cert_pack (#pm: perm) (#x: t_Certificate) (#v: asn1_t X.k_Certificate) ()
  requires cert_flat pm x v
  ensures arel true d_Certificate pm x v
{
  unfold cert_flat;
  tbs_eq (pm /. 2.0R) x.tbsCertificate.value (fst v);
  rewrite (tbs_rel (pm /. 2.0R) x.tbsCertificate.value (fst v)) as (arel true dbase_TBSCertificate (pm /. 2.0R) x.tbsCertificate.value (fst v));
  fold (tbs_kept_rel pm x.tbsCertificate (fst v));
  tbs_kept_eq pm x.tbsCertificate (fst v);
  rewrite (tbs_kept_rel pm x.tbsCertificate (fst v)) as (arel true d_TBSCertificate pm x.tbsCertificate (fst v));
  fold (cert_rel pm x v);
  cert_eq pm x v;
  rewrite (cert_rel pm x v) as (arel true d_Certificate pm x v)
}

(** {2 Field tests} *)

(** A slice over the first [n] bytes of an array. *)
fn prefix_slice (a: A.array U8.t) (#p: perm) (#v: Ghost.erased (Seq.seq U8.t)) (n: SZ.t{SZ.v n <= Seq.length v})
  requires A.pts_to a #p v ** pure (SZ.v n <= Seq.length v)
  returns s: S.slice U8.t
  ensures S.pts_to s #p (Seq.slice v 0 (SZ.v n)) **
          trade (S.pts_to s #p (Seq.slice v 0 (SZ.v n))) (A.pts_to a #p v)
{
  let ap = AP.from_array a;
  let rest = AP.ghost_split ap n;
  let s = S.arrayptr_to_slice_intro ap n;
  intro_trade (S.pts_to s #p (Seq.slice v 0 (SZ.v n))) (A.pts_to a #p v)
    (AP.is_from_array ap (Seq.length v) a **
     AP.pts_to (reveal rest) #p (Seq.slice v (SZ.v n) (Seq.length v)) **
     S.arrayptr_to_slice ap s **
     pure (AP.adjacent ap (SZ.v n) rest)) fn _ {
    S.arrayptr_to_slice_elim s;
    AP.join ap #p #(Seq.slice v 0 (SZ.v n)) (reveal rest) #(Seq.slice v (SZ.v n) (Seq.length v));
    Seq.lemma_split v (SZ.v n);
    rewrite (AP.pts_to ap #p (Seq.append (Seq.slice v 0 (SZ.v n)) (Seq.slice v (SZ.v n) (Seq.length v))))
         as (AP.pts_to ap #p v);
    AP.to_array ap a;
  };
  s
}


(* A test that a slice holds exactly the literal [l]. *)
inline_for_extraction noextract
let lit_t (l: Ghost.erased (list U8.t)) =
  (s: S.slice U8.t) -> (#pm: perm) -> (#w: Ghost.erased (Seq.seq U8.t)) ->
  stt bool (S.pts_to s #pm w) (fun r -> S.pts_to s #pm w ** pure (r <==> KS.bytes_is w l))

(* Whether a slice related to a value by [enc] holds exactly the literal [l]. *)
inline_for_extraction noextract
fn ser_is (#u: Type0) (enc: u -> GTot (Seq.seq U8.t)) (l: Ghost.erased (list U8.t)) (f: lit_t l)
  (s: S.slice U8.t) (#pm: perm) (#y: Ghost.erased u)
  requires prel_slice_ser enc pm s y
  returns r: bool
  ensures prel_slice_ser enc pm s y ** pure (r <==> KS.bytes_is (enc y) l)
{
  unfold (prel_slice_ser enc pm s y);
  with w. assert (S.pts_to s #pm w);
  let r = f s #pm #w;
  fold (prel_slice_ser enc pm s y);
  r
}

ghost
fn opt_none_elim (#t: Type0) (#u: Type0) (r: prel t u) (pm: perm) (y: option u)
  requires prel_option r pm None y
  ensures prel_option r pm None y ** pure (None? y)
{
  if (Some? y) {
    rewrite (prel_option r pm None y) as (pure False);
    unreachable ()
  } else {
    ()
  }
}

ghost
fn opt_some_elim (#t: Type0) (#u: Type0) (r: prel t u) (pm: perm) (a: t) (y: option u)
  requires prel_option r pm (Some a) y
  returns b: Ghost.erased u
  ensures r pm a b ** pure (y == Some (reveal b))
{
  match y {
    Some b -> {
      rewrite (prel_option r pm (Some a) y) as (r pm a b);
      hide b
    }
    None -> {
      rewrite (prel_option r pm (Some a) y) as (pure False);
      unreachable ()
    }
  }
}

ghost
fn opt_some_intro (#t: Type0) (#u: Type0) (r: prel t u) (pm: perm) (a: t) (b: u) (y: option u)
  requires r pm a b ** pure (y == Some b)
  ensures prel_option r pm (Some a) y
{
  rewrite (r pm a b) as (prel_option r pm (Some a) y)
}

inline_for_extraction noextract
fn params_is (lp: Ghost.erased (list U8.t)) (fp: lit_t lp)
  (x: t_AlgorithmIdentifier_parameters_opt) (#pm: perm) (#y: Ghost.erased (option asn1_value))
  requires prel_option any_rel pm (oview_AlgorithmIdentifier_parameters x) y
  returns r: bool
  ensures prel_option any_rel pm (oview_AlgorithmIdentifier_parameters x) y **
          pure (r <==> KS.params_are y lp)
{
  match x {
    AlgorithmIdentifier_parameters_absent -> {
      rewrite (prel_option any_rel pm (oview_AlgorithmIdentifier_parameters x) y)
           as (prel_option any_rel pm None y);
      opt_none_elim any_rel pm y;
      rewrite (prel_option any_rel pm None y)
           as (prel_option any_rel pm (oview_AlgorithmIdentifier_parameters x) y);
      false
    }
    AlgorithmIdentifier_parameters_present ps -> {
      rewrite (prel_option any_rel pm (oview_AlgorithmIdentifier_parameters x) y)
           as (prel_option any_rel pm (Some ps) y);
      let b = opt_some_elim any_rel pm ps y;
      unfold any_rel;
      let r = ser_is VE.asn1_value_enc lp fp ps;
      fold (any_rel pm ps b);
      opt_some_intro any_rel pm ps b y;
      rewrite (prel_option any_rel pm (Some ps) y)
           as (prel_option any_rel pm (oview_AlgorithmIdentifier_parameters x) y);
      r
    }
  }
}

(* An AlgorithmIdentifier with OID [lo] and parameters encoded as [lp]. *)
inline_for_extraction noextract
fn alg_is (lo: Ghost.erased (list U8.t)) (fo: lit_t lo) (lp: Ghost.erased (list U8.t)) (fp: lit_t lp)
  (a: t_AlgorithmIdentifier) (#pm: perm) (#v: Ghost.erased (asn1_t X.k_AlgorithmIdentifier))
  requires arel true d_AlgorithmIdentifier pm a v
  returns r: bool
  ensures arel true d_AlgorithmIdentifier pm a v **
          pure (r <==> (KS.oid_is (XP.alg_oid v) lo /\ KS.params_are (XP.alg_params v) lp))
{
  alg_eq pm a v;
  rewrite (arel true d_AlgorithmIdentifier pm a v) as (alg_rel pm a v);
  unfold alg_rel;
  unfold oid_rel;
  let ro = ser_is (E.leaf_enc ASN1_OID) lo fo a.algorithm;
  fold (oid_rel pm a.algorithm (fst v));
  let rp = params_is lp fp a.parameters;
  fold (alg_rel pm a v);
  rewrite (alg_rel pm a v) as (arel true d_AlgorithmIdentifier pm a v);
  (ro && rp)
}

