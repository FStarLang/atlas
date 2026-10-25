module TLS13.X509.Spec

(** X.509 certificate path validation for TLS server authentication.

    [validate_chain] is RFC 5280 6.1 path validation and RFC 6125 name
    matching in a strict, fail-closed profile:

    - Certificates are DER, walked with [TLS13.Crypto.Spec.der_tlv]
      (single-byte tags, definite minimal lengths below 64 KiB).
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
    - Signatures are sha{256,384,512}WithRSAEncryption by RSA keys and
      ecdsa-with-SHA256 by P-256 keys.
    - Trust anchors are only a subject name and public key: their validity,
      extensions and signatures are not checked. *)

module B = TLS13.Bytes
module T = TLS13.Types
module C = TLS13.Crypto.Spec
module Seq = FStar.Seq
module U8 = FStar.UInt8

type certificate = B.bytes
type cert_chain = list certificate

(** The trust anchors are a concatenation of DER certificates. *)
type trust_store = {
  anchors: B.bytes;
}

type validation_time = {
  seconds_since_epoch: nat;
}

type peer_identity = {
  validated_hostname: T.hostname;
  leaf_public_key: C.public_key;
  permitted_signature_schemes: list T.signature_scheme;
}

(** {2 Bytes} *)

let bytes_eq (a b:B.bytes) : bool = Seq.eq a b

let rec mem_bytes (x:B.bytes) (l:list B.bytes) : bool =
  match l with
  | [] -> false
  | y :: r -> bytes_eq x y || mem_bytes x r

(** [c[s, e)] is exactly [l]. *)
let rec range_is (c:B.bytes) (s e:nat) (l:list U8.t) : Tot bool (decreases l) =
  match l with
  | [] -> s = e
  | x :: r -> s < e && e <= B.length c && Seq.index c s = x && range_is c (s + 1) e r

let bytes_are (c:B.bytes) (l:list U8.t) : bool = range_is c 0 (B.length c) l

(** The content range of the DER TLV at [pos], whatever its tag. *)
let der_any (c:B.bytes) (pos limit:nat)
  : option (r:(nat & nat){
      pos + 2 <= fst r /\ fst r <= snd r /\ snd r <= limit /\ limit <= B.length c}) =
  if pos < limit && limit <= B.length c then C.der_tlv c (Seq.index c pos) pos limit
  else None

(** {2 Time}

    [Time ::= CHOICE { utcTime UTCTime, generalTime GeneralizedTime }] in the
    DER forms RFC 5280 4.1.2.5 prescribes: [YYMMDDHHMMSSZ] (years 1950 to
    2049) and [YYYYMMDDHHMMSSZ], as seconds since 1970-01-01T00:00:00Z.
    Leap seconds are rejected. *)

let is_digit (x:U8.t) : bool = 0x30 <= U8.v x && U8.v x <= 0x39

let digit (x:U8.t) : nat = if is_digit x then U8.v x - 0x30 else 0

(** The decimal value of the [n] digits at [c[s]]. *)
let rec dec (c:B.bytes) (s:nat) (n:nat{s + n <= B.length c}) : Tot nat (decreases n) =
  if n = 0 then 0 else 10 * dec c s (n - 1) + digit (Seq.index c (s + n - 1))

let rec all_digits (c:B.bytes) (s:nat) (n:nat{s + n <= B.length c}) : Tot bool (decreases n) =
  n = 0 || (is_digit (Seq.index c (s + n - 1)) && all_digits c s (n - 1))

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
let days_before_year (y:pos) : int =
  let p = y - 1 in
  365 * p + p / 4 - p / 100 + p / 400

(** [days_before_year 1970]. *)
let epoch_days : int = 719162

(** The UTC instant [y-m-d h:mi:s] in seconds since the epoch, if valid. *)
let instant (y m dd h mi s:nat) : option int =
  if 1 <= y && 1 <= m && m <= 12 && 1 <= dd && dd <= days_in_month y m &&
     h < 24 && mi < 60 && s < 60
  then Some ((days_before_year y + days_before_month y m + (dd - 1) - epoch_days) * 86400 +
             h * 3600 + mi * 60 + s)
  else None

(** The [Time] at [pos] and its end. *)
let parse_time (c:B.bytes) (pos limit:nat) : option (int & nat) =
  match C.der_tlv c 0x17uy pos limit with
  | Some (s, e) ->
    if e = s + 13 && all_digits c s 12 && Seq.index c (s + 12) = 0x5Auy then
      let yy = dec c s 2 in
      let y = if yy < 50 then 2000 + yy else 1900 + yy in
      (match instant y (dec c (s + 2) 2) (dec c (s + 4) 2)
                       (dec c (s + 6) 2) (dec c (s + 8) 2) (dec c (s + 10) 2) with
       | Some t -> Some (t, e)
       | None -> None)
    else None
  | None ->
    match C.der_tlv c 0x18uy pos limit with
    | Some (s, e) ->
      if e = s + 15 && all_digits c s 14 && Seq.index c (s + 14) = 0x5Auy then
        (match instant (dec c s 4) (dec c (s + 4) 2) (dec c (s + 6) 2)
                       (dec c (s + 8) 2) (dec c (s + 10) 2) (dec c (s + 12) 2) with
         | Some t -> Some (t, e)
         | None -> None)
      else None
    | None -> None

(** {2 Extensions} *)

type extension = {
  ext_oid: B.bytes;
  ext_critical: bool;
  ext_value: B.bytes;
}

(** [Extension ::= SEQUENCE { extnID OBJECT IDENTIFIER, critical BOOLEAN
    DEFAULT FALSE, extnValue OCTET STRING }], repeated over [c[pos, limit)].
    In DER a FALSE [critical] is omitted. *)
let rec parse_extensions (c:B.bytes) (pos limit:nat)
  : Tot (option (list extension)) (decreases (if limit > pos then limit - pos else 0)) =
  if pos >= limit then (if pos = limit then Some [] else None)
  else
    match C.der_tlv c 0x30uy pos limit with
    | None -> None
    | Some (es, ee) ->
      match C.der_tlv c 0x06uy es ee with
      | None -> None
      | Some (os, oe) ->
        let crit : option (bool & nat) =
          match C.der_tlv c 0x01uy oe ee with
          | Some (bs, be) ->
            if be = bs + 1 && Seq.index c bs = 0xFFuy then Some (true, be) else None
          | None -> Some (false, oe) in
        match crit with
        | None -> None
        | Some (critical, vpos) ->
          match C.der_tlv c 0x04uy vpos ee with
          | None -> None
          | Some (vs, ve) ->
            if ve <> ee then None
            else
              match parse_extensions c ee limit with
              | None -> None
              | Some rest ->
                Some ({ ext_oid = Seq.slice c os oe;
                        ext_critical = critical;
                        ext_value = Seq.slice c vs ve } :: rest)

let oid_basic_constraints : list U8.t = [0x55uy; 0x1Duy; 0x13uy]
let oid_key_usage : list U8.t = [0x55uy; 0x1Duy; 0x0Fuy]
let oid_subject_alt_name : list U8.t = [0x55uy; 0x1Duy; 0x11uy]
let oid_ext_key_usage : list U8.t = [0x55uy; 0x1Duy; 0x25uy]
let oid_name_constraints : list U8.t = [0x55uy; 0x1Duy; 0x1Euy]

let rec find_extension (exts:list extension) (oid:list U8.t) : option B.bytes =
  match exts with
  | [] -> None
  | x :: r -> if bytes_are x.ext_oid oid then Some x.ext_value else find_extension r oid

let rec oid_in (oid:B.bytes) (exts:list extension) : bool =
  match exts with
  | [] -> false
  | x :: r -> bytes_eq oid x.ext_oid || oid_in oid r

let understood (x:extension) : bool =
  bytes_are x.ext_oid oid_basic_constraints ||
  bytes_are x.ext_oid oid_key_usage ||
  bytes_are x.ext_oid oid_subject_alt_name ||
  bytes_are x.ext_oid oid_ext_key_usage

(** No extension appears twice (RFC 5280 4.2), every critical one is
    understood, and there are no name constraints, which are not
    supported. *)
let rec extensions_ok (exts:list extension) : bool =
  match exts with
  | [] -> true
  | x :: r ->
    not (oid_in x.ext_oid r) &&
    (not x.ext_critical || understood x) &&
    not (bytes_are x.ext_oid oid_name_constraints) &&
    extensions_ok r

(** [BasicConstraints ::= SEQUENCE { cA BOOLEAN DEFAULT FALSE,
    pathLenConstraint INTEGER (0..MAX) OPTIONAL }] as [(cA, pathLen)].  A
    pathLenConstraint needs cA and is at most 127. *)
let basic_constraints (v:B.bytes) : option (bool & option nat) =
  match C.der_tlv v 0x30uy 0 (B.length v) with
  | None -> None
  | Some (s, e) ->
    if e <> B.length v then None
    else
      let ca : option (bool & nat) =
        match C.der_tlv v 0x01uy s e with
        | Some (bs, be) ->
          if be = bs + 1 && Seq.index v bs = 0xFFuy then Some (true, be) else None
        | None -> Some (false, s) in
      match ca with
      | None -> None
      | Some (ca, p) ->
        if p = e then Some (ca, None)
        else
          match C.der_tlv v 0x02uy p e with
          | Some (is, ie) ->
            if ca && ie = e && ie = is + 1 && U8.v (Seq.index v is) < 0x80
            then Some (true, Some (U8.v (Seq.index v is)))
            else None
          | None -> None

(** The first byte of [KeyUsage ::= BIT STRING]: bit 0 (digitalSignature)
    is [0x80], bit 5 (keyCertSign) is [0x04]. *)
let key_usage_bits (v:B.bytes) : option U8.t =
  match C.der_tlv v 0x03uy 0 (B.length v) with
  | None -> None
  | Some (s, e) ->
    if e <> B.length v || s >= e || U8.v (Seq.index v s) > 7 then None
    else if s + 1 = e then Some 0uy
    else Some (Seq.index v (s + 1))

let has_bit (b mask:U8.t) : bool = U8.logand b mask <> 0uy

let key_usage_allows (exts:list extension) (mask:U8.t) : bool =
  match find_extension exts oid_key_usage with
  | None -> true
  | Some v ->
    (match key_usage_bits v with
     | Some b -> has_bit b mask
     | None -> false)

(** id-kp-serverAuth (1.3.6.1.5.5.7.3.1) and anyExtendedKeyUsage
    (2.5.29.37.0). *)
let oid_server_auth : list U8.t = [0x2Buy; 0x06uy; 0x01uy; 0x05uy; 0x05uy; 0x07uy; 0x03uy; 0x01uy]
let oid_any_eku : list U8.t = [0x55uy; 0x1Duy; 0x25uy; 0x00uy]

(** Whether the OIDs over [v[pos, limit)] include serverAuth, if they are
    all well formed. *)
let rec eku_server_auth (v:B.bytes) (pos limit:nat)
  : Tot (option bool) (decreases (if limit > pos then limit - pos else 0)) =
  if pos >= limit then (if pos = limit then Some false else None)
  else
    match C.der_tlv v 0x06uy pos limit with
    | None -> None
    | Some (s, e) ->
      match eku_server_auth v e limit with
      | None -> None
      | Some found ->
        Some (found || range_is v s e oid_server_auth || range_is v s e oid_any_eku)

(** [ExtKeyUsageSyntax ::= SEQUENCE SIZE (1..MAX) OF KeyPurposeId], if
    present, allows TLS server authentication. *)
let ext_key_usage_ok (exts:list extension) : bool =
  match find_extension exts oid_ext_key_usage with
  | None -> true
  | Some v ->
    (match C.der_tlv v 0x30uy 0 (B.length v) with
     | Some (s, e) -> e = B.length v && eku_server_auth v s e = Some true
     | None -> false)

(** {2 Server names} *)

let lower (x:U8.t) : U8.t =
  if 0x41 <= U8.v x && U8.v x <= 0x5A then U8.add x 0x20uy else x

(** [a[ai, ai+n)] and [b[bi, bi+n)] are equal up to ASCII case. *)
let rec ci_eq (a:B.bytes) (ai:nat) (b:B.bytes) (bi:nat)
  (n:nat{ai + n <= B.length a /\ bi + n <= B.length b})
  : Tot bool (decreases n) =
  n = 0 ||
  (lower (Seq.index a (ai + n - 1)) = lower (Seq.index b (bi + n - 1)) &&
   ci_eq a ai b bi (n - 1))

(** [a[s, s+n)] has no ['.']. *)
let rec dot_free (a:B.bytes) (s:nat) (n:nat{s + n <= B.length a}) : Tot bool (decreases n) =
  n = 0 || (Seq.index a (s + n - 1) <> 0x2Euy && dot_free a s (n - 1))

(** A dNSName [p] names host [h] (RFC 6125 6.4): exactly, up to ASCII case,
    or as [*.rest] with [rest] of at least two labels, matching [h] past
    its first label. *)
let dns_matches (p h:B.bytes) : bool =
  let lp = B.length p in
  let lh = B.length h in
  (lp > 0 && lp = lh && ci_eq p 0 h 0 lp) ||
  (lp >= 4 && Seq.index p 0 = 0x2Auy && Seq.index p 1 = 0x2Euy &&
   not (dot_free p 2 (lp - 2)) &&
   lh >= lp &&
   dot_free h 0 (lh - (lp - 1)) &&
   ci_eq p 1 h (lh - (lp - 1)) (lp - 1))

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

(** The four bytes of [h] as a dotted-decimal IPv4 address. *)
let ipv4_address (h:B.bytes) : option B.bytes =
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
          if p = B.length h then Some (Seq.seq_of_list [a; b; c; d]) else None

(** Whether a [GeneralName] over [v[pos, limit)] names the host: a dNSName
    ([2]) when [ip] is [None], an iPAddress ([7]) equal to [ip] otherwise. *)
let rec general_names_match (v:B.bytes) (pos limit:nat) (h:B.bytes) (ip:option B.bytes)
  : Tot (option bool) (decreases (if limit > pos then limit - pos else 0)) =
  if pos >= limit then (if pos = limit then Some false else None)
  else
    match der_any v pos limit with
    | None -> None
    | Some (s, e) ->
      match general_names_match v e limit h ip with
      | None -> None
      | Some found ->
        let tag = Seq.index v pos in
        let this =
          match ip with
          | Some a -> tag = 0x87uy && bytes_eq (Seq.slice v s e) a
          | None -> tag = 0x82uy && dns_matches (Seq.slice v s e) h in
        Some (found || this)

(** The subjectAltName names [hostname]. *)
let subject_alt_name_ok (exts:list extension) (hostname:B.bytes) : bool =
  match find_extension exts oid_subject_alt_name with
  | None -> false
  | Some v ->
    (match C.der_tlv v 0x30uy 0 (B.length v) with
     | Some (s, e) ->
       e = B.length v && B.length hostname > 0 &&
       general_names_match v s e hostname (ipv4_address hostname) = Some true
     | None -> false)

(** {2 Certificates} *)

type tbs_fields = {
  version: nat;
  tbs_signature_algorithm: B.bytes;  (* AlgorithmIdentifier contents *)
  issuer: B.bytes;                   (* Name, DER *)
  not_before: int;
  not_after: int;
  subject: B.bytes;                  (* Name, DER *)
  extensions: list extension;
}

(** [TBSCertificate] contents [c[ts, te)] (RFC 5280 4.1). *)
let parse_tbs (c:B.bytes) (ts te:nat) : option tbs_fields =
  let ver : option (nat & nat) =
    match C.der_tlv c 0xA0uy ts te with
    | Some (vs, ve) ->
      (match C.der_tlv c 0x02uy vs ve with
       | Some (is, ie) ->
         if ie = ve && ie = is + 1 && (Seq.index c is = 1uy || Seq.index c is = 2uy)
         then Some (U8.v (Seq.index c is) + 1, ve)
         else None
       | None -> None)
    | None -> Some (1, ts) in
  match ver with
  | None -> None
  | Some (version, p) ->
  match C.der_tlv c 0x02uy p te with  (* serialNumber *)
  | None -> None
  | Some (_, serial_end) ->
  match C.der_tlv c 0x30uy serial_end te with  (* signature *)
  | None -> None
  | Some (a_s, a_e) ->
  match C.der_tlv c 0x30uy a_e te with  (* issuer *)
  | None -> None
  | Some (_, issuer_end) ->
  match C.der_tlv c 0x30uy issuer_end te with  (* validity *)
  | None -> None
  | Some (vs, ve) ->
  match parse_time c vs ve with
  | None -> None
  | Some (not_before, p1) ->
  match parse_time c p1 ve with
  | None -> None
  | Some (not_after, p2) ->
  if p2 <> ve then None else
  match C.der_tlv c 0x30uy ve te with  (* subject *)
  | None -> None
  | Some (_, subject_end) ->
  match C.der_tlv c 0x30uy subject_end te with  (* subjectPublicKeyInfo *)
  | None -> None
  | Some (_, spki_end) ->
  let p : nat = match C.der_tlv c 0x81uy spki_end te with Some r -> snd r | None -> spki_end in
  let p : nat = match C.der_tlv c 0x82uy p te with Some r -> snd r | None -> p in
  let exts : option (list extension) =
    if p = te then Some []
    else
      match C.der_tlv c 0xA3uy p te with
      | Some (xs, xe) ->
        if xe <> te || version <> 3 then None
        else
          (match C.der_tlv c 0x30uy xs xe with
           | Some (ls, le) -> if le <> xe then None else parse_extensions c ls le
           | None -> None)
      | None -> None in
  match exts with
  | None -> None
  | Some extensions ->
    Some {
      version;
      tbs_signature_algorithm = Seq.slice c a_s a_e;
      issuer = Seq.slice c a_e issuer_end;
      not_before;
      not_after;
      subject = Seq.slice c ve subject_end;
      extensions;
    }

type parsed_certificate = {
  tbs: B.bytes;                  (* the signed TBSCertificate, DER *)
  fields: tbs_fields;
  signature_algorithm: B.bytes;  (* AlgorithmIdentifier contents *)
  signature_value: B.bytes;      (* BIT STRING contents past the unused-bits byte *)
}

(** [Certificate ::= SEQUENCE { tbsCertificate, signatureAlgorithm,
    signatureValue BIT STRING }] spanning all of [c]. *)
let parse_certificate (c:B.bytes) : option parsed_certificate =
  match C.der_tlv c 0x30uy 0 (B.length c) with
  | None -> None
  | Some (cs, ce) ->
  if ce <> B.length c then None else
  match C.der_tlv c 0x30uy cs ce with
  | None -> None
  | Some (ts, te) ->
  match C.der_tlv c 0x30uy te ce with
  | None -> None
  | Some (a_s, a_e) ->
  match C.der_tlv c 0x03uy a_e ce with
  | None -> None
  | Some (bs, be) ->
  if be <> ce || bs >= be || Seq.index c bs <> 0x00uy then None else
  match parse_tbs c ts te with
  | None -> None
  | Some fields ->
    Some {
      tbs = Seq.slice c cs te;
      fields;
      signature_algorithm = Seq.slice c a_s a_e;
      signature_value = Seq.slice c (bs + 1) be;
    }

(** {2 Signatures} *)

(** sha256/384/512WithRSAEncryption (1.2.840.113549.1.1.11/12/13) with NULL
    parameters (RFC 4055 5). *)
let sha_with_rsa (a:B.bytes) (last:U8.t) : bool =
  bytes_are a [0x06uy; 0x09uy; 0x2Auy; 0x86uy; 0x48uy; 0x86uy; 0xF7uy; 0x0Duy;
               0x01uy; 0x01uy; last; 0x05uy; 0x00uy]

(** ecdsa-with-SHA256 (1.2.840.10045.4.3.2) without parameters (RFC 5758 3.2). *)
let ecdsa_with_sha256 (a:B.bytes) : bool =
  bytes_are a [0x06uy; 0x08uy; 0x2Auy; 0x86uy; 0x48uy; 0xCEuy; 0x3Duy; 0x04uy;
               0x03uy; 0x02uy]

(** [child]'s signature verifies under the public key of certificate
    [issuer]. *)
let signed_by (child:parsed_certificate) (issuer:certificate) : GTot bool =
  match C.certificate_raw_public_key issuer with
  | Some (C.RawRsa n e) ->
    if sha_with_rsa child.signature_algorithm 0x0Buy then
      C.rsa_pkcs1_verify C.Pkcs1Sha256 n e child.tbs child.signature_value
    else if sha_with_rsa child.signature_algorithm 0x0Cuy then
      C.rsa_pkcs1_verify C.Pkcs1Sha384 n e child.tbs child.signature_value
    else if sha_with_rsa child.signature_algorithm 0x0Duy then
      C.rsa_pkcs1_verify C.Pkcs1Sha512 n e child.tbs child.signature_value
    else false
  | Some (C.RawP256 q) ->
    ecdsa_with_sha256 child.signature_algorithm &&
    C.ecdsa_secp256r1_sha256_verify q child.tbs child.signature_value
  | None -> false

(** {2 Paths} *)

(** What every path certificate satisfies at time [t]. *)
let path_certificate_ok (pc:parsed_certificate) (t:nat) : bool =
  pc.fields.version = 3 &&
  bytes_eq pc.signature_algorithm pc.fields.tbs_signature_algorithm &&
  pc.fields.not_before <= t && t <= pc.fields.not_after &&
  extensions_ok pc.fields.extensions &&
  ext_key_usage_ok pc.fields.extensions

(** What the leaf satisfies for [hostname]. *)
let leaf_ok (pc:parsed_certificate) (hostname:B.bytes) : bool =
  subject_alt_name_ok pc.fields.extensions hostname &&
  key_usage_allows pc.fields.extensions 0x80uy

(** What a path certificate issuing others satisfies, with [below]
    intermediate certificates between it and the leaf. *)
let issuer_ok (pc:parsed_certificate) (below:nat) : bool =
  (match find_extension pc.fields.extensions oid_basic_constraints with
   | Some v ->
     (match basic_constraints v with
      | Some (true, None) -> true
      | Some (true, Some n) -> below <= n
      | _ -> false)
   | None -> false) &&
  key_usage_allows pc.fields.extensions 0x04uy

(** The certificates in a concatenation of DER certificates [a[pos ..]]. *)
let rec anchor_list (a:B.bytes) (pos:nat)
  : Tot (option (list certificate)) (decreases (if B.length a > pos then B.length a - pos else 0)) =
  if pos >= B.length a then Some []
  else
    match C.der_tlv a 0x30uy pos (B.length a) with
    | None -> None
    | Some (_, e) ->
      match anchor_list a e with
      | None -> None
      | Some rest -> Some (Seq.slice a pos e :: rest)

(** Some anchor's subject is [child]'s issuer and its key signed [child]. *)
let rec anchored (anchors:list certificate) (child:parsed_certificate)
  : GTot bool (decreases anchors) =
  match anchors with
  | [] -> false
  | a :: rest ->
    (match parse_certificate a with
     | Some pa -> bytes_eq pa.fields.subject child.fields.issuer && signed_by child a
     | None -> false) ||
    anchored rest child

(** [child], at [depth] in the path, chains to a trust anchor through a
    prefix of [rest]. *)
let rec chains (anchors:list certificate) (t:nat) (child:parsed_certificate)
  (depth:nat) (rest:cert_chain)
  : GTot bool (decreases rest) =
  anchored anchors child ||
  (match rest with
   | [] -> false
   | next :: rest' ->
     (match parse_certificate next with
      | Some pn ->
        path_certificate_ok pn t &&
        issuer_ok pn depth &&
        bytes_eq child.fields.issuer pn.fields.subject &&
        signed_by child next &&
        chains anchors t pn (depth + 1) rest'
      | None -> false))

[@@"opaque_to_smt"]
let validate_chain
  (hostname:T.hostname)
  (validation_time:validation_time)
  (trust_store:trust_store)
  (certs:cert_chain)
  : GTot (option peer_identity) =
  let t = validation_time.seconds_since_epoch in
  match certs, anchor_list trust_store.anchors 0 with
  | leaf :: rest, Some anchors ->
    (match parse_certificate leaf with
     | Some pl ->
       if path_certificate_ok pl t && leaf_ok pl hostname &&
          (mem_bytes leaf anchors || chains anchors t pl 0 rest)
       then Some {
         validated_hostname = hostname;
         leaf_public_key = leaf;
         permitted_signature_schemes = [];
       }
       else None
     | None -> None)
  | _, _ -> None
