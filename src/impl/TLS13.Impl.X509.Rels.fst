module TLS13.Impl.X509.Rels

(** The relations between the parsed values of the certificate fields that
    path validation reads and their ASN.1 values, unfolded one level (see
    [TLS13.Impl.X509.ASN1]). *)

#lang-pulse

open Pulse.Lib.Pervasives
open ASN1.Base
open ASN1.Pulse.Rel
open TLS13.Wire.Generated.X509.Impl
open TLS13.Impl.X509.ASN1

module C = TLS13.X509.Chain
module E = ASN1.Spec.Content.Enc
module PS = ASN1.Pulse.ParseSeqOf
module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module X = TLS13.Wire.Generated.X509
module XP = TLS13.X509.Profile

(** {2 Extension} *)

let crit_m (pm: perm) (x: t_Extension_critical_opt) (y: XP.extension) : slprop =
  match x, fst (snd y) with
  | Extension_critical_absent, Default -> emp
  | Extension_critical_present a, Nondefault b -> pure (a == b)
  | _ -> pure False

let ext_rel (pm: perm) (x: t_Extension) (y: XP.extension) : slprop =
  oid_rel pm x.extnID (fst y) **
  (crit_m pm x.critical y **
   prel_slice_ser (E.leaf_enc ASN1_OCTETSTRING) pm x.extnValue (snd (snd y)))

let ext_eq (pm: perm) (x: t_Extension) (y: XP.extension)
: Lemma (arel true d_Extension pm x y == ext_rel pm x y)
= assert (arel true d_Extension pm x y == ext_rel pm x y)
    by (FStar.Tactics.norm [delta_only [`%arel; `%crel; `%irel; `%drel; `%asn1_terminal_rel; `%coerce_eq; `%prel_eq;
          `%d_Extension; `%cd_Extension; `%view_Extension; `%oview_Extension_critical; `%ext_rel; `%crit_m; `%oid_rel]; zeta; iota; primops];
        FStar.Tactics.smt ())

let rtac' (z: bool) (l: list string) : FStar.Tactics.Tac unit =
  FStar.Tactics.norm [delta_only (l @ [`%arel; `%crel; `%irel; `%drel; `%lcrel; `%asn1_terminal_rel; `%coerce_eq; `%prel_eq;
     `%prel_option; `%oid_rel; `%any_rel; `%alg_rel]); (if z then zeta_full else zeta); iota; primops];
  FStar.Tactics.smt ()

let rtac = rtac' false

(** {2 Version} *)

let ver_m (pm: perm) (x: t_TBSCertificate_version_opt) (t: XP.tbs) : slprop =
  match x, XP.tbs_version t with
  | TBSCertificate_version_absent, Default -> emp
  | TBSCertificate_version_present a, Nondefault b -> asn1_int_rel asn1_any_integer_bound pm a b
  | _ -> pure False

let ver_eq (pm: perm) (x: t_TBSCertificate_version_opt) (t: XP.tbs)
: Lemma (ver_rel pm x (fst t) == ver_m pm x t)
= assert (ver_rel pm x (fst t) == ver_m pm x t)
    by (rtac [`%ver_rel; `%ver_m; `%oview_TBSCertificate_version; `%XP.tbs_version; `%asn1_int_rel])

(** {2 Extensions} *)

let exts_eq (pm: perm) (e: ml t_Extension) (y: _)
: Lemma (arel true (D_ILC (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 3) (CD_PREFIXED d_Extensions)) pm e y ==
         PS.ml_match d_Extension pm e y)
= assert (arel true (D_ILC (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 3) (CD_PREFIXED d_Extensions)) pm e y ==
          PS.ml_match d_Extension pm e y)
    by (rtac [`%d_Extensions; `%cd_Extensions; `%PS.ml_match; `%PS.ml_match0])

(** {2 Validity} *)

let validity_rel (pm: perm) (x: t_Validity) (y: asn1_t X.k_Validity) : slprop =
  arel true d_Time pm x.notBefore (fst y) ** arel true d_Time pm x.notAfter (snd y)

let validity_eq (pm: perm) (x: t_Validity) (y: asn1_t X.k_Validity)
: Lemma (arel true d_Validity pm x y == validity_rel pm x y)
= assert (arel true d_Validity pm x y == validity_rel pm x y)
    by (rtac [`%d_Validity; `%cd_Validity; `%view_Validity; `%validity_rel])

let time_m (pm: perm) (x: t_Time) (y: asn1_t X.k_Time) : slprop =
  match x with
  | Time_utcTime s ->
    if dfst y = C.id_utc_time then prel_slice_ser (E.leaf_enc ASN1_UTCTIME) pm s (C.time_utc y) else pure False
  | Time_generalTime s ->
    if dfst y = C.id_generalized_time then prel_slice_ser (E.leaf_enc ASN1_GENERALIZEDTIME) pm s (C.time_generalized y) else pure False

let time_eq (pm: perm) (x: t_Time) (y: asn1_t X.k_Time)
: Lemma (arel true d_Time pm x y == time_m pm x y)
= let (| id, v |) = y in
  match x with
  | Time_utcTime s ->
    assert (arel true d_Time pm (Time_utcTime s) (| id, v |) == time_m pm (Time_utcTime s) (| id, v |))
      by (rtac [`%d_Time; `%view_Time; `%time_m; `%C.time_utc; `%C.time_generalized; `%C.id_utc_time; `%C.id_generalized_time])
  | Time_generalTime s ->
    assert (arel true d_Time pm (Time_generalTime s) (| id, v |) == time_m pm (Time_generalTime s) (| id, v |))
      by (rtac' true [`%d_Time; `%view_Time; `%time_m; `%C.time_utc; `%C.time_generalized; `%C.id_utc_time; `%C.id_generalized_time;
                `%ASN1.Syntax.mk_constant_id])

(** {2 Names} *)

let name_rel (pm: perm) (x: t_Name_kept) (y: XP.name) : slprop =
  arel true dbase_Name (pm /. 2.0R) x.value y **
  keep_rel X.k_Name (pm /. 2.0R) (kview_Name x).kraw y **
  pure (Some? (kview_Name x).kraw)

let name_eq (pm: perm) (x: t_Name_kept) (y: XP.name)
: Lemma (arel true d_Name pm x y == name_rel pm x y)
= assert (arel true d_Name pm x y == name_rel pm x y)
    by (FStar.Tactics.norm [delta_only [`%arel; `%d_Name; `%name_rel]; zeta; iota; primops];
        FStar.Tactics.trefl ())

(** {2 BasicConstraints} *)

let bc_m (pm: perm) (x: t_BasicConstraints) (y: asn1_t X.k_BasicConstraints) : slprop =
  (match x.cA, fst y with
   | BasicConstraints_cA_absent, Default -> emp
   | BasicConstraints_cA_present a, Nondefault b -> pure (a == b)
   | _ -> pure False) **
  (match x.pathLenConstraint, snd y with
   | BasicConstraints_pathLenConstraint_absent, None -> emp
   | BasicConstraints_pathLenConstraint_present a, Some b -> asn1_int_rel asn1_any_integer_bound pm a b
   | _ -> pure False)

let bc_eq (pm: perm) (x: t_BasicConstraints) (y: asn1_t X.k_BasicConstraints)
: Lemma (arel true d_BasicConstraints pm x y == bc_m pm x y)
= let bc_case (c: t_BasicConstraints_cA_opt) (p: t_BasicConstraints_pathLenConstraint_opt)
    : Lemma (arel true d_BasicConstraints pm (Mkt_BasicConstraints c p) y == bc_m pm (Mkt_BasicConstraints c p) y)
    = match c, p with
      | BasicConstraints_cA_absent, BasicConstraints_pathLenConstraint_absent ->
        assert (arel true d_BasicConstraints pm (Mkt_BasicConstraints BasicConstraints_cA_absent BasicConstraints_pathLenConstraint_absent) y ==
                bc_m pm (Mkt_BasicConstraints BasicConstraints_cA_absent BasicConstraints_pathLenConstraint_absent) y)
          by (rtac [`%d_BasicConstraints; `%cd_BasicConstraints; `%view_BasicConstraints; `%bc_m;
                    `%oview_BasicConstraints_cA; `%oview_BasicConstraints_pathLenConstraint; `%asn1_int_rel])
      | BasicConstraints_cA_present a, BasicConstraints_pathLenConstraint_absent ->
        assert (arel true d_BasicConstraints pm (Mkt_BasicConstraints (BasicConstraints_cA_present a) BasicConstraints_pathLenConstraint_absent) y ==
                bc_m pm (Mkt_BasicConstraints (BasicConstraints_cA_present a) BasicConstraints_pathLenConstraint_absent) y)
          by (rtac [`%d_BasicConstraints; `%cd_BasicConstraints; `%view_BasicConstraints; `%bc_m;
                    `%oview_BasicConstraints_cA; `%oview_BasicConstraints_pathLenConstraint; `%asn1_int_rel])
      | BasicConstraints_cA_absent, BasicConstraints_pathLenConstraint_present b ->
        assert (arel true d_BasicConstraints pm (Mkt_BasicConstraints BasicConstraints_cA_absent (BasicConstraints_pathLenConstraint_present b)) y ==
                bc_m pm (Mkt_BasicConstraints BasicConstraints_cA_absent (BasicConstraints_pathLenConstraint_present b)) y)
          by (rtac [`%d_BasicConstraints; `%cd_BasicConstraints; `%view_BasicConstraints; `%bc_m;
                    `%oview_BasicConstraints_cA; `%oview_BasicConstraints_pathLenConstraint; `%asn1_int_rel])
      | BasicConstraints_cA_present a, BasicConstraints_pathLenConstraint_present b ->
        assert (arel true d_BasicConstraints pm (Mkt_BasicConstraints (BasicConstraints_cA_present a) (BasicConstraints_pathLenConstraint_present b)) y ==
                bc_m pm (Mkt_BasicConstraints (BasicConstraints_cA_present a) (BasicConstraints_pathLenConstraint_present b)) y)
          by (rtac [`%d_BasicConstraints; `%cd_BasicConstraints; `%view_BasicConstraints; `%bc_m;
                    `%oview_BasicConstraints_cA; `%oview_BasicConstraints_pathLenConstraint; `%asn1_int_rel])
  in
  bc_case x.cA x.pathLenConstraint

(** {2 KeyUsage, ExtKeyUsageSyntax} *)

let ku_eq (pm: perm) (x: asn1_bitstring_impl) (y: asn1_t X.k_KeyUsage)
: Lemma (arel true d_KeyUsage pm x y == asn1_bitstring_rel pm x y)
= assert (arel true d_KeyUsage pm x y == asn1_bitstring_rel pm x y)
    by (rtac [`%d_KeyUsage; `%cd_KeyUsage])

let eku_eq (pm: perm) (x: ml (S.slice U8.t)) (y: asn1_t X.k_ExtKeyUsageSyntax)
: Lemma (arel true d_ExtKeyUsageSyntax pm x y == PS.ml_match d_KeyPurposeId pm x y)
= assert (arel true d_ExtKeyUsageSyntax pm x y == PS.ml_match d_KeyPurposeId pm x y)
    by (rtac [`%d_ExtKeyUsageSyntax; `%cd_ExtKeyUsageSyntax; `%PS.ml_match; `%PS.ml_match0])

let kp_eq (pm: perm) (x: S.slice U8.t) (y: asn1_t X.k_KeyPurposeId)
: Lemma (arel true d_KeyPurposeId pm x y == oid_rel pm x y)
= assert (arel true d_KeyPurposeId pm x y == oid_rel pm x y)
    by (rtac [`%d_KeyPurposeId; `%cd_KeyPurposeId])

(** {2 GeneralNames} *)

let gns_eq (pm: perm) (x: ml t_GeneralName) (y: asn1_t X.k_GeneralNames)
: Lemma (arel true d_GeneralNames pm x y == PS.ml_match d_GeneralName pm x y)
= assert (arel true d_GeneralNames pm x y == PS.ml_match d_GeneralName pm x y)
    by (rtac [`%d_GeneralNames; `%cd_GeneralNames; `%PS.ml_match; `%PS.ml_match0])

let gn_dns_m (pm: perm) (s: S.slice U8.t) (y: asn1_t X.k_GeneralName) : slprop =
  if dfst y = C.id_dns_name then prel_slice_ser (E.leaf_enc ASN1_IA5STRING) pm s (C.gn_dns_name y) else pure False

let gn_dns_eq (pm: perm) (s: S.slice U8.t) (y: asn1_t X.k_GeneralName)
: Lemma (arel true d_GeneralName pm (GeneralName_dNSName s) y == gn_dns_m pm s y)
= let (| id, v |) = y in
  assert (arel true d_GeneralName pm (GeneralName_dNSName s) (| id, v |) == gn_dns_m pm s (| id, v |))
    by (rtac' true [`%d_GeneralName; `%view_GeneralName; `%gn_dns_m; `%C.gn_dns_name; `%C.id_dns_name; `%ASN1.Syntax.mk_custom_id])

let gn_ip_m (pm: perm) (s: S.slice U8.t) (y: asn1_t X.k_GeneralName) : slprop =
  if dfst y = C.id_ip_address then prel_slice_ser (E.leaf_enc ASN1_OCTETSTRING) pm s (C.gn_ip_address y) else pure False

let gn_ip_eq (pm: perm) (s: S.slice U8.t) (y: asn1_t X.k_GeneralName)
: Lemma (arel true d_GeneralName pm (GeneralName_iPAddress s) y == gn_ip_m pm s y)
= let (| id, v |) = y in
  assert (arel true d_GeneralName pm (GeneralName_iPAddress s) (| id, v |) == gn_ip_m pm s (| id, v |))
    by (rtac' true [`%d_GeneralName; `%view_GeneralName; `%gn_ip_m; `%C.gn_ip_address; `%C.id_ip_address; `%ASN1.Syntax.mk_custom_id])
