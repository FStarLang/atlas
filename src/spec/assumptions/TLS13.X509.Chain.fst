module TLS13.X509.Chain

(** X.509 certificate path validation for TLS server authentication, over
    the ASN.1 values of the certificates ([TLS13.X509.Profile]): this is the
    definition of [TLS13.X509.Spec.validate_chain].

    It is RFC 5280 6.1 path validation and RFC 6125 name matching in a
    strict, fail-closed profile:

    - Certificates are the DER encodings of [Certificate] in the RFC 5280
      profile [src/asn1/X509.asn], parsed with the parser everparse-asn1
      generates from it.
    - The path is a prefix of the certificates the peer sent, in order: the
      leaf, then each certificate issuing the previous one, until one is
      issued by a trust anchor (or the leaf is itself a trust anchor).  Names
      are compared as DER bytes.
    - Every path certificate is v3, has matching inner and outer signature
      algorithms, is valid at the validation time, has no duplicate
      extensions, no critical extension other than basicConstraints,
      keyUsage, subjectAltName and extKeyUsage, no nameConstraints, and an
      extKeyUsage, if any, allowing serverAuth.
    - Issuing path certificates are CAs (basicConstraints cA) within their
      pathLenConstraint, with keyCertSign if they carry keyUsage.
    - The leaf names the server in its subjectAltName (dNSName with an
      optional leftmost [*] label, or iPAddress for an IPv4 literal; the
      subject CN is never used) and has digitalSignature if it carries
      keyUsage.
    - Signatures are sha{256,384,512}WithRSAEncryption by RSA keys,
      ecdsa-with-SHA256 and ecdsa-with-SHA384 by P-256 and P-384 keys, over
      the DER [TBSCertificate], in a BIT STRING without unused bits.
    - Trust anchors are only a subject name and public key: their validity,
      extensions and signatures are not checked. *)

open ASN1.Base

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module E = ASN1.Spec.Content.Enc
module KS = TLS13.X509.KeySpec
module Seq = FStar.Seq
module Ser = ASN1.Spec.Serializer
module U8 = FStar.UInt8
module VE = ASN1.Spec.Value.Enc
module X = TLS13.Wire.Generated.X509
module XP = TLS13.X509.Profile

(** {2 Bytes} *)

let byte_is (c:B.bytes) (i:nat) (x:U8.t) : bool = i < B.length c && Seq.index c i = x

(** [a[ai, ai+n)] and [b[bi, bi+n)] are the same bytes. *)
let rec same_bytes (a:B.bytes) (ai:nat) (b:B.bytes) (bi:nat) (n:nat) : Tot bool (decreases n) =
  n = 0 ||
  (ai < B.length a && bi < B.length b && Seq.index a ai = Seq.index b bi &&
   same_bytes a (ai + 1) b (bi + 1) (n - 1))

(** [a[a0, a1)] and [b[b0, b1)] are the same bytes. *)
let range_eq (a:B.bytes) (a0 a1:nat) (b:B.bytes) (b0 b1:nat) : bool =
  a0 <= a1 && b0 <= b1 && a1 - a0 = b1 - b0 && same_bytes a a0 b b0 (a1 - a0)

(** {2 Time}

    [Time ::= CHOICE { utcTime UTCTime, generalTime GeneralizedTime }] in the
    DER forms RFC 5280 4.1.2.5 prescribes: [YYMMDDHHMMSSZ] (years 1950 to
    2049) and [YYYYMMDDHHMMSSZ], as seconds since 0001-01-01T00:00:00Z.
    Leap seconds are rejected. *)

let is_digit (x:U8.t) : bool = 0x30 <= U8.v x && U8.v x <= 0x39

let digit (x:U8.t) : nat = if is_digit x then U8.v x - 0x30 else 0

let rec all_digits (c:B.bytes) (s e:nat) : Tot bool (decreases (if e > s then e - s else 0)) =
  s >= e || (s < B.length c && is_digit (Seq.index c s) && all_digits c (s + 1) e)

(** The decimal values of the two and four digits at [c[s]]. *)
let dec2 (c:B.bytes) (s:nat) : nat =
  if s + 2 <= B.length c then 10 * digit (Seq.index c s) + digit (Seq.index c (s + 1)) else 0

let dec4 (c:B.bytes) (s:nat) : nat = 100 * dec2 c s + dec2 c (s + 2)

let is_leap (y:nat) : bool = (y % 4 = 0 && y % 100 <> 0) || y % 400 = 0

let days_in_month (y m:nat) : nat =
  if m = 2 then (if is_leap y then 29 else 28)
  else if m = 4 || m = 6 || m = 9 || m = 11 then 30
  else 31

let days_before_month (y m:nat) : nat =
  let base =
    if m <= 1 then 0 else if m = 2 then 31 else if m = 3 then 59
    else if m = 4 then 90 else if m = 5 then 120 else if m = 6 then 151
    else if m = 7 then 181 else if m = 8 then 212 else if m = 9 then 243
    else if m = 10 then 273 else if m = 11 then 304 else 334 in
  if m > 2 && is_leap y then base + 1 else base

(** Days from 0001-01-01 to [y]-01-01 in the proleptic Gregorian calendar. *)
let days_before_year (y:pos) : nat =
  let p = y - 1 in
  365 * p + p / 4 - p / 100 + p / 400

(** Seconds from 0001-01-01 to 1970-01-01: [days_before_year 1970 * 86400]. *)
let epoch_seconds : nat = 62135596800

(** The UTC instant [y-m-d h:mi:s] in seconds since 0001-01-01, if valid. *)
let instant (y m dd h mi s:nat) : option nat =
  if 1 <= y && 1 <= m && m <= 12 && 1 <= dd && dd <= days_in_month y m &&
     h < 24 && mi < 60 && s < 60
  then Some ((days_before_year y + days_before_month y m + (dd - 1)) * 86400 +
             h * 3600 + mi * 60 + s)
  else None

(** A UTCTime [YYMMDDHHMMSSZ]. *)
let utc_time (c:B.bytes) : option nat =
  if B.length c = 13 && all_digits c 0 12 && byte_is c 12 0x5Auy then
    let yy = dec2 c 0 in
    let y = if yy < 50 then 2000 + yy else 1900 + yy in
    instant y (dec2 c 2) (dec2 c 4) (dec2 c 6) (dec2 c 8) (dec2 c 10)
  else None

(** A GeneralizedTime [YYYYMMDDHHMMSSZ]. *)
let generalized_time (c:B.bytes) : option nat =
  if B.length c = 15 && all_digits c 0 14 && byte_is c 14 0x5Auy then
    instant (dec4 c 0) (dec2 c 4) (dec2 c 6) (dec2 c 8) (dec2 c 10) (dec2 c 12)
  else None

let id_utc_time : asn1_id_t = ASN1.Syntax.mk_constant_id 23
let id_generalized_time : asn1_id_t = ASN1.Syntax.mk_constant_id 24

let time_utc (y:asn1_t X.k_Time) : Pure asn1_utctime_t (requires dfst y == id_utc_time) (ensures fun _ -> True) =
  assert_norm (idlookup_t id_utc_time (asn1_lc_t X.lc_Time) == asn1_utctime_t);
  coerce_eq () (dsnd y)

let time_generalized (y:asn1_t X.k_Time)
  : Pure asn1_generalizedtime_t (requires dfst y == id_generalized_time) (ensures fun _ -> True) =
  assert_norm (idlookup_t id_generalized_time (asn1_lc_t X.lc_Time) == asn1_generalizedtime_t);
  coerce_eq () (dsnd y)

(** A [Time] in seconds since 0001-01-01. *)
let time_value (y:asn1_t X.k_Time) : option nat =
  if dfst y = id_utc_time then utc_time (E.leaf_enc ASN1_UTCTIME (time_utc y))
  else if dfst y = id_generalized_time then
    generalized_time (E.leaf_enc ASN1_GENERALIZEDTIME (time_generalized y))
  else None

(** {2 Extensions} *)

let ext_oid_bytes (x:XP.extension) : B.bytes = E.leaf_enc ASN1_OID (XP.ext_oid x)

(** The extension's OID is [2.5.29.k] ([55 1D k]). *)
let ext_is (x:XP.extension) (k:U8.t) : bool = KS.bytes_is (ext_oid_bytes x) [0x55uy; 0x1Duy; k]

let oid_basic_constraints : U8.t = 0x13uy
let oid_key_usage : U8.t = 0x0Fuy
let oid_subject_alt_name : U8.t = 0x11uy
let oid_ext_key_usage : U8.t = 0x25uy
let oid_name_constraints : U8.t = 0x1Euy

(** The extensions of a [TBSCertificate]: none if absent. *)
let exts (t:XP.tbs) : list XP.extension =
  match XP.tbs_extensions t with
  | Some l -> l
  | None -> []

(** The value of the first extension [2.5.29.k]. *)
let rec find_extension (l:list XP.extension) (k:U8.t) : option B.bytes =
  match l with
  | [] -> None
  | x :: tl -> if ext_is x k then Some (XP.ext_value x) else find_extension tl k

(** Some extension has the OID [o]. *)
let rec oid_in (o:B.bytes) (l:list XP.extension) : bool =
  match l with
  | [] -> false
  | x :: tl -> Seq.eq o (ext_oid_bytes x) || oid_in o tl

let understood (x:XP.extension) : bool =
  ext_is x oid_basic_constraints || ext_is x oid_key_usage ||
  ext_is x oid_subject_alt_name || ext_is x oid_ext_key_usage

(** No extension appears twice (RFC 5280 4.2), every critical one is
    understood, and there are no name constraints, which are not
    supported. *)
let rec extensions_ok (l:list XP.extension) : bool =
  match l with
  | [] -> true
  | x :: tl ->
    not (oid_in (ext_oid_bytes x) tl) &&
    (not (XP.ext_critical x) || understood x) &&
    not (ext_is x oid_name_constraints) &&
    extensions_ok tl

(** The [BasicConstraints] [v] make a CA that may have [below] intermediate
    certificates under it. *)
let ca_allows (v:B.bytes) (below:nat) : GTot bool =
  match XP.parse_full X.k_BasicConstraints v with
  | Some bc ->
    v_of_default (fst bc) &&
    (match snd bc with
     | None -> true
     | Some n -> below <= n)
  | None -> false

(** The first byte of [KeyUsage ::= BIT STRING] [v]: bit 0
    (digitalSignature) is [0x80], bit 5 (keyCertSign) is [0x04]. *)
let key_usage_bits (v:B.bytes) : GTot (option U8.t) =
  match XP.parse_full X.k_KeyUsage v with
  | Some ku ->
    let b = BYTES_WITH_UNUSEDBITS?.b ku in
    Some (if Seq.length b = 0 then 0uy else Seq.index b 0)
  | None -> None

let has_bit (b mask:U8.t) : bool = U8.logand b mask <> 0uy

(** There is no keyUsage, or one with a bit of [mask]. *)
let key_usage_allows (l:list XP.extension) (mask:U8.t) : GTot bool =
  match find_extension l oid_key_usage with
  | None -> true
  | Some v ->
    (match key_usage_bits v with
     | Some b -> has_bit b mask
     | None -> false)

(** id-kp-serverAuth (1.3.6.1.5.5.7.3.1) and anyExtendedKeyUsage
    (2.5.29.37.0). *)
let server_auth_oid : list U8.t = [0x2Buy; 0x06uy; 0x01uy; 0x05uy; 0x05uy; 0x07uy; 0x03uy; 0x01uy]
let any_eku_oid : list U8.t = [0x55uy; 0x1Duy; 0x25uy; 0x00uy]

let purpose_bytes (o:asn1_t X.k_KeyPurposeId) : B.bytes = E.leaf_enc ASN1_OID o

let rec eku_server_auth (l:list (asn1_t X.k_KeyPurposeId)) : bool =
  match l with
  | [] -> false
  | o :: tl ->
    KS.bytes_is (purpose_bytes o) server_auth_oid ||
    KS.bytes_is (purpose_bytes o) any_eku_oid ||
    eku_server_auth tl

(** [ExtKeyUsageSyntax ::= SEQUENCE SIZE (1..MAX) OF KeyPurposeId], if
    present, allows TLS server authentication. *)
let ext_key_usage_ok (l:list XP.extension) : GTot bool =
  match find_extension l oid_ext_key_usage with
  | None -> true
  | Some v ->
    (match XP.parse_full X.k_ExtKeyUsageSyntax v with
     | Some ks -> eku_server_auth ks
     | None -> false)

(** {2 Server names} *)

let lower (x:U8.t) : U8.t =
  if 0x41 <= U8.v x && U8.v x <= 0x5A then U8.add x 0x20uy else x

(** [a[ai, ai+n)] and [b[bi, bi+n)] are equal up to ASCII case. *)
let rec ci_eq (a:B.bytes) (ai:nat) (b:B.bytes) (bi:nat) (n:nat) : Tot bool (decreases n) =
  n = 0 ||
  (ai < B.length a && bi < B.length b &&
   lower (Seq.index a ai) = lower (Seq.index b bi) &&
   ci_eq a (ai + 1) b (bi + 1) (n - 1))

(** [a[s, s+n)] has no ['.']. *)
let rec dot_free (a:B.bytes) (s:nat) (n:nat) : Tot bool (decreases n) =
  n = 0 || (s < B.length a && Seq.index a s <> 0x2Euy && dot_free a (s + 1) (n - 1))

(** A dNSName [c[ps, pe)] names host [h] (RFC 6125 6.4): exactly, up to
    ASCII case, or as [*.rest] with [rest] of at least two labels, matching
    [h] past its first label. *)
let dns_matches (c:B.bytes) (ps pe:nat) (h:B.bytes) : bool =
  ps <= pe &&
  (let lp = pe - ps in
   let lh = B.length h in
   (lp > 0 && lp = lh && ci_eq c ps h 0 lp) ||
   (lp >= 4 && byte_is c ps 0x2Auy && byte_is c (ps + 1) 0x2Euy &&
    not (dot_free c (ps + 2) (lp - 2)) &&
    lh >= lp &&
    dot_free h 0 (lh - (lp - 1)) &&
    ci_eq c (ps + 1) h (lh - (lp - 1)) (lp - 1)))

(** The decimal octet at [h[pos]] and its end: one to three digits, no
    leading zero, at most 255. *)
let dec_octet (h:B.bytes) (pos:nat) : option (U8.t & nat) =
  let n = B.length h in
  if not (pos < n && is_digit (Seq.index h pos)) then None
  else
    let d0 = digit (Seq.index h pos) in
    if not (pos + 1 < n && is_digit (Seq.index h (pos + 1))) then
      Some (U8.uint_to_t d0, pos + 1)
    else if d0 = 0 then None
    else
      let d1 = digit (Seq.index h (pos + 1)) in
      if not (pos + 2 < n && is_digit (Seq.index h (pos + 2))) then
        Some (U8.uint_to_t (10 * d0 + d1), pos + 2)
      else if pos + 3 < n && is_digit (Seq.index h (pos + 3)) then None
      else
        let v = 100 * d0 + 10 * d1 + digit (Seq.index h (pos + 2)) in
        if v > 255 then None else Some (U8.uint_to_t v, pos + 3)

(** The decimal octet after a ['.'] at [h[pos]]. *)
let dot_octet (h:B.bytes) (pos:nat) : option (U8.t & nat) =
  if pos < B.length h && Seq.index h pos = 0x2Euy then dec_octet h (pos + 1) else None

type ipv4 = {
  ip0: U8.t;
  ip1: U8.t;
  ip2: U8.t;
  ip3: U8.t;
}

(** [h] as a dotted-decimal IPv4 address. *)
let ipv4_address (h:B.bytes) : option ipv4 =
  match dec_octet h 0 with
  | None -> None
  | Some (a, p) ->
    match dot_octet h p with
    | None -> None
    | Some (b, p) ->
      match dot_octet h p with
      | None -> None
      | Some (c, p) ->
        match dot_octet h p with
        | None -> None
        | Some (d, p) ->
          if p = B.length h then Some ({ ip0 = a; ip1 = b; ip2 = c; ip3 = d }) else None

let ip_is (c:B.bytes) (a:ipv4) : bool =
  B.length c = 4 &&
  byte_is c 0 a.ip0 && byte_is c 1 a.ip1 && byte_is c 2 a.ip2 && byte_is c 3 a.ip3

let id_dns_name : asn1_id_t = ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC PRIMITIVE 2
let id_ip_address : asn1_id_t = ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC PRIMITIVE 7

let gn_dns_name (g:asn1_t X.k_GeneralName)
  : Pure asn1_ia5string_t (requires dfst g == id_dns_name) (ensures fun _ -> True) =
  assert_norm (idlookup_t id_dns_name (asn1_lc_t X.lc_GeneralName) == asn1_ia5string_t);
  coerce_eq () (dsnd g)

let gn_ip_address (g:asn1_t X.k_GeneralName)
  : Pure asn1_octetstring_t (requires dfst g == id_ip_address) (ensures fun _ -> True) =
  assert_norm (idlookup_t id_ip_address (asn1_lc_t X.lc_GeneralName) == asn1_octetstring_t);
  coerce_eq () (dsnd g)

(** A [GeneralName] names the host: a dNSName when [ip] is [None], an
    iPAddress equal to [ip] otherwise. *)
let gn_matches (h:B.bytes) (ip:option ipv4) (g:asn1_t X.k_GeneralName) : bool =
  match ip with
  | Some a -> dfst g = id_ip_address && ip_is (E.leaf_enc ASN1_OCTETSTRING (gn_ip_address g)) a
  | None ->
    dfst g = id_dns_name &&
    (let c = E.leaf_enc ASN1_IA5STRING (gn_dns_name g) in dns_matches c 0 (B.length c) h)

let rec names_match (h:B.bytes) (ip:option ipv4) (l:list (asn1_t X.k_GeneralName)) : bool =
  match l with
  | [] -> false
  | g :: tl -> gn_matches h ip g || names_match h ip tl

(** The subjectAltName names [hostname]. *)
let subject_alt_name_ok (l:list XP.extension) (hostname:B.bytes) : GTot bool =
  match find_extension l oid_subject_alt_name with
  | None -> false
  | Some v ->
    B.length hostname > 0 &&
    (match XP.parse_full X.k_GeneralNames v with
     | Some gs -> names_match hostname (ipv4_address hostname) gs
     | None -> false)

(** {2 Certificates} *)

(** The DER certificate [c]. *)
let parse_certificate (c:B.bytes) : GTot (option XP.certificate) = XP.parse_full X.k_Certificate c

let is_v3 (t:XP.tbs) : bool =
  match XP.tbs_version t with
  | Nondefault v -> v = 2
  | Default -> false

(** Two [AlgorithmIdentifier]s are the same. *)
let alg_same (a b:XP.alg_id) : bool =
  Seq.eq (E.leaf_enc ASN1_OID (XP.alg_oid a)) (E.leaf_enc ASN1_OID (XP.alg_oid b)) &&
  (match XP.alg_params a, XP.alg_params b with
   | None, None -> true
   | Some p, Some q -> Seq.eq (VE.asn1_value_enc p) (VE.asn1_value_enc q)
   | _ -> false)

let valid_at (t:XP.tbs) (now:nat) : bool =
  match time_value (fst (XP.tbs_validity t)), time_value (snd (XP.tbs_validity t)) with
  | Some nb, Some na -> nb <= now && now <= na
  | _ -> false

let name_bytes (n:XP.name) : GTot B.bytes = Ser.asn1_enc X.k_Name n

let tbs_bytes (c:XP.certificate) : GTot B.bytes = Ser.asn1_enc X.k_TBSCertificate (XP.cert_tbs c)

(** sha256/384/512WithRSAEncryption (1.2.840.113549.1.1.11/12/13) with NULL
    parameters (RFC 4055 5), and ecdsa-with-SHA256/384
    (1.2.840.10045.4.3.2/3) without parameters (RFC 5758 3.2). *)
let sha256_rsa_oid : list U8.t = [0x2Auy; 0x86uy; 0x48uy; 0x86uy; 0xF7uy; 0x0Duy; 0x01uy; 0x01uy; 0x0Buy]
let sha384_rsa_oid : list U8.t = [0x2Auy; 0x86uy; 0x48uy; 0x86uy; 0xF7uy; 0x0Duy; 0x01uy; 0x01uy; 0x0Cuy]
let sha512_rsa_oid : list U8.t = [0x2Auy; 0x86uy; 0x48uy; 0x86uy; 0xF7uy; 0x0Duy; 0x01uy; 0x01uy; 0x0Duy]
let ecdsa_sha256_oid : list U8.t = [0x2Auy; 0x86uy; 0x48uy; 0xCEuy; 0x3Duy; 0x04uy; 0x03uy; 0x02uy]
let ecdsa_sha384_oid : list U8.t = [0x2Auy; 0x86uy; 0x48uy; 0xCEuy; 0x3Duy; 0x04uy; 0x03uy; 0x03uy]

let rsa_alg (a:XP.alg_id) (o:list U8.t) : bool =
  KS.oid_is (XP.alg_oid a) o && KS.params_are (XP.alg_params a) KS.der_null

let ecdsa_alg (a:XP.alg_id) (o:list U8.t) : bool =
  KS.oid_is (XP.alg_oid a) o && None? (XP.alg_params a)

(** The signature of certificate [child] verifies under the public key of
    the DER certificate [issuer]. *)
let signed_by (child:XP.certificate) (issuer:B.bytes) : GTot bool =
  let a = XP.cert_sig_alg child in
  let sg = XP.cert_sig child in
  let tbs = tbs_bytes child in
  let s = BYTES_WITH_UNUSEDBITS?.b sg in
  BYTES_WITH_UNUSEDBITS?.unused sg = 0uy &&
  (match C.certificate_raw_public_key issuer with
   | Some (C.RawRsa n e) ->
     if rsa_alg a sha256_rsa_oid then C.rsa_pkcs1_verify C.Pkcs1Sha256 n e tbs s
     else if rsa_alg a sha384_rsa_oid then C.rsa_pkcs1_verify C.Pkcs1Sha384 n e tbs s
     else if rsa_alg a sha512_rsa_oid then C.rsa_pkcs1_verify C.Pkcs1Sha512 n e tbs s
     else false
   | Some (C.RawP256 q) ->
     if ecdsa_alg a ecdsa_sha256_oid then C.ecdsa_secp256r1_sha256_verify q tbs s
     else if ecdsa_alg a ecdsa_sha384_oid then C.ecdsa_secp256r1_sha384_verify q tbs s
     else false
   | Some (C.RawP384 q) ->
     if ecdsa_alg a ecdsa_sha256_oid then C.ecdsa_secp384r1_sha256_verify q tbs s
     else if ecdsa_alg a ecdsa_sha384_oid then C.ecdsa_secp384r1_sha384_verify q tbs s
     else false
   | None -> false)

(** {2 Paths} *)

(** What every path certificate satisfies at [t] seconds since 1970. *)
let path_ok (c:XP.certificate) (t:nat) : GTot bool =
  let tb = XP.cert_tbs c in
  is_v3 tb &&
  alg_same (XP.cert_sig_alg c) (XP.tbs_sig_alg tb) &&
  valid_at tb (t + epoch_seconds) &&
  extensions_ok (exts tb) &&
  ext_key_usage_ok (exts tb)

(** What the leaf satisfies for [hostname]. *)
let leaf_ok (c:XP.certificate) (hostname:B.bytes) : GTot bool =
  subject_alt_name_ok (exts (XP.cert_tbs c)) hostname &&
  key_usage_allows (exts (XP.cert_tbs c)) 0x80uy

(** What a path certificate issuing others satisfies, with [below]
    intermediate certificates between it and the leaf. *)
let issuer_ok (c:XP.certificate) (below:nat) : GTot bool =
  (match find_extension (exts (XP.cert_tbs c)) oid_basic_constraints with
   | Some v -> ca_allows v below
   | None -> false) &&
  key_usage_allows (exts (XP.cert_tbs c)) 0x04uy

(** [parent]'s subject is [child]'s issuer. *)
let names_issuer (child parent:XP.certificate) : GTot bool =
  Seq.eq (name_bytes (XP.tbs_issuer (XP.cert_tbs child)))
         (name_bytes (XP.tbs_subject (XP.cert_tbs parent)))

(** [a[pos ..]] is a concatenation of DER certificates. *)
let rec anchors_wf (a:B.bytes) (pos:nat)
  : Tot bool (decreases (if B.length a > pos then B.length a - pos else 0)) =
  pos >= B.length a ||
  (match C.der_tlv a 0x30uy pos (B.length a) with
   | None -> false
   | Some (_, e) -> anchors_wf a e)

(** [leaf] is one of the certificates over [a[pos ..]]. *)
let rec is_anchor (leaf:B.bytes) (a:B.bytes) (pos:nat)
  : Tot bool (decreases (if B.length a > pos then B.length a - pos else 0)) =
  pos < B.length a &&
  (match C.der_tlv a 0x30uy pos (B.length a) with
   | None -> false
   | Some (_, e) -> range_eq leaf 0 (B.length leaf) a pos e || is_anchor leaf a e)

(** Trust anchor [anc]'s subject is [child]'s issuer and its key signed
    [child]. *)
let anchor_issues (anc:B.bytes) (child:XP.certificate) : GTot bool =
  match parse_certificate anc with
  | Some av -> names_issuer child av && signed_by child anc
  | None -> false

(** Some trust anchor over [a[pos ..]] issued [child]. *)
let rec anchored (a:B.bytes) (pos:nat) (child:XP.certificate)
  : GTot bool (decreases (if B.length a > pos then B.length a - pos else 0)) =
  pos < B.length a &&
  (match C.der_tlv a 0x30uy pos (B.length a) with
   | None -> false
   | Some (_, e) -> anchor_issues (Seq.slice a pos e) child || anchored a e child)

(** [child], at [depth] in the path, chains to a trust anchor through a
    prefix of [rest]. *)
let rec chains (a:B.bytes) (t:nat) (child:XP.certificate) (depth:nat) (rest:list B.bytes)
  : GTot bool (decreases rest) =
  anchored a 0 child ||
  (match rest with
   | [] -> false
   | next :: rest' ->
     (match parse_certificate next with
      | Some pn ->
        path_ok pn t &&
        issuer_ok pn depth &&
        names_issuer child pn &&
        signed_by child next &&
        chains a t pn (depth + 1) rest'
      | None -> false))

(** The peer's certificates [certs] are a valid path for [hostname] at [t]
    seconds since 1970 to one of the trust anchors [a]. *)
let chain_ok (hostname:B.bytes) (t:nat) (a:B.bytes) (certs:list B.bytes) : GTot bool =
  match certs with
  | leaf :: rest ->
    anchors_wf a 0 &&
    (match parse_certificate leaf with
     | Some pl ->
       path_ok pl t && leaf_ok pl hostname &&
       (is_anchor leaf a 0 || chains a t pl 0 rest)
     | None -> false)
  | [] -> false
