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
      extensions and signatures are not checked.

    It is written over positions in whole DER certificates, and every
    recursion is a tail-recursive scan, so that the verified validator in
    [TLS13.Impl.X509.Validate] is a transcription of it. *)

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

let byte_is (c:B.bytes) (i:nat) (x:U8.t) : bool = i < B.length c && Seq.index c i = x

(** [a[ai, ai+n)] and [b[bi, bi+n)] are the same bytes. *)
let rec same_bytes (a:B.bytes) (ai:nat) (b:B.bytes) (bi:nat) (n:nat) : Tot bool (decreases n) =
  n = 0 ||
  (ai < B.length a && bi < B.length b && Seq.index a ai = Seq.index b bi &&
   same_bytes a (ai + 1) b (bi + 1) (n - 1))

(** [a[a0, a1)] and [b[b0, b1)] are the same bytes. *)
let range_eq (a:B.bytes) (a0 a1:nat) (b:B.bytes) (b0 b1:nat) : bool =
  a0 <= a1 && b0 <= b1 && a1 - a0 = b1 - b0 && same_bytes a a0 b b0 (a1 - a0)

(** [c[s, e)], or nothing if that is not a range of [c]. *)
let sub (c:B.bytes) (s e:nat) : B.bytes =
  if s <= e && e <= B.length c then Seq.slice c s e else Seq.empty

(** The content range of the DER TLV at [pos], whatever its tag. *)
let der_any (c:B.bytes) (pos limit:nat)
  : option (r:(nat & nat){
      pos + 2 <= fst r /\ fst r <= snd r /\ snd r <= limit /\ limit <= B.length c}) =
  if pos < limit && limit <= B.length c then C.der_tlv c (Seq.index c pos) pos limit
  else None

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

(** The [Time] at [pos] and its end. *)
let parse_time (c:B.bytes) (pos limit:nat) : option (nat & nat) =
  match C.der_tlv c 0x17uy pos limit with
  | Some (s, e) ->
    if e = s + 13 && all_digits c s (s + 12) && byte_is c (s + 12) 0x5Auy then
      let yy = dec2 c s in
      let y = if yy < 50 then 2000 + yy else 1900 + yy in
      (match instant y (dec2 c (s + 2)) (dec2 c (s + 4))
                       (dec2 c (s + 6)) (dec2 c (s + 8)) (dec2 c (s + 10)) with
       | Some t -> Some (t, e)
       | None -> None)
    else None
  | None ->
    match C.der_tlv c 0x18uy pos limit with
    | Some (s, e) ->
      if e = s + 15 && all_digits c s (s + 14) && byte_is c (s + 14) 0x5Auy then
        (match instant (dec4 c s) (dec2 c (s + 4)) (dec2 c (s + 6))
                       (dec2 c (s + 8)) (dec2 c (s + 10)) (dec2 c (s + 12)) with
         | Some t -> Some (t, e)
         | None -> None)
      else None
    | None -> None

(** {2 Extensions} *)

(** The ranges of one [Extension] in a certificate. *)
type extension = {
  oid_s: nat;
  oid_e: nat;
  critical: bool;
  value_s: nat;
  value_e: nat;
  ext_end: nat;
}

(** [Extension ::= SEQUENCE { extnID OBJECT IDENTIFIER, critical BOOLEAN
    DEFAULT FALSE, extnValue OCTET STRING }] at [c[pos, limit)].  In DER a
    FALSE [critical] is omitted. *)
let ext_at (c:B.bytes) (pos limit:nat)
  : option (x:extension{pos < x.ext_end /\ x.ext_end <= limit}) =
  match C.der_tlv c 0x30uy pos limit with
  | None -> None
  | Some (es, ee) ->
    match C.der_tlv c 0x06uy es ee with
    | None -> None
    | Some (os, oe) ->
      let crit : option (bool & nat) =
        match C.der_tlv c 0x01uy oe ee with
        | Some (bs, be) ->
          if be = bs + 1 && byte_is c bs 0xFFuy then Some (true, be) else None
        | None -> Some (false, oe) in
      match crit with
      | None -> None
      | Some (critical, vpos) ->
        match C.der_tlv c 0x04uy vpos ee with
        | None -> None
        | Some (vs, ve) ->
          if ve <> ee then None
          else Some ({ oid_s = os; oid_e = oe; critical; value_s = vs; value_e = ve;
                       ext_end = ee })

(** [c[pos, limit)] is a sequence of extensions. *)
let rec extensions_wf (c:B.bytes) (pos limit:nat)
  : Tot bool (decreases (if limit > pos then limit - pos else 0)) =
  if pos >= limit then pos = limit
  else
    match ext_at c pos limit with
    | None -> false
    | Some x -> extensions_wf c x.ext_end limit

(** The extension's OID is [2.5.29.k] ([55 1D k]). *)
let ext_oid_is (c:B.bytes) (x:extension) (k:U8.t) : bool =
  x.oid_e = x.oid_s + 3 &&
  byte_is c x.oid_s 0x55uy && byte_is c (x.oid_s + 1) 0x1Duy && byte_is c (x.oid_s + 2) k

let oid_basic_constraints : U8.t = 0x13uy
let oid_key_usage : U8.t = 0x0Fuy
let oid_subject_alt_name : U8.t = 0x11uy
let oid_ext_key_usage : U8.t = 0x25uy
let oid_name_constraints : U8.t = 0x1Euy

(** The value range of the first extension [2.5.29.k] over [c[pos, limit)]. *)
let rec find_extension (c:B.bytes) (pos limit:nat) (k:U8.t)
  : Tot (option (nat & nat)) (decreases (if limit > pos then limit - pos else 0)) =
  if pos >= limit then None
  else
    match ext_at c pos limit with
    | None -> None
    | Some x ->
      if ext_oid_is c x k then Some (x.value_s, x.value_e)
      else find_extension c x.ext_end limit k

(** Some extension over [c[pos, limit)] has the OID [c[os, oe)]. *)
let rec oid_in (c:B.bytes) (os oe:nat) (pos limit:nat)
  : Tot bool (decreases (if limit > pos then limit - pos else 0)) =
  if pos >= limit then false
  else
    match ext_at c pos limit with
    | None -> false
    | Some x -> range_eq c os oe c x.oid_s x.oid_e || oid_in c os oe x.ext_end limit

let understood (c:B.bytes) (x:extension) : bool =
  ext_oid_is c x oid_basic_constraints ||
  ext_oid_is c x oid_key_usage ||
  ext_oid_is c x oid_subject_alt_name ||
  ext_oid_is c x oid_ext_key_usage

(** No extension appears twice (RFC 5280 4.2), every critical one is
    understood, and there are no name constraints, which are not
    supported. *)
let rec extensions_ok (c:B.bytes) (pos limit:nat)
  : Tot bool (decreases (if limit > pos then limit - pos else 0)) =
  if pos >= limit then true
  else
    match ext_at c pos limit with
    | None -> false
    | Some x ->
      not (oid_in c x.oid_s x.oid_e x.ext_end limit) &&
      (not x.critical || understood c x) &&
      not (ext_oid_is c x oid_name_constraints) &&
      extensions_ok c x.ext_end limit

(** [BasicConstraints ::= SEQUENCE { cA BOOLEAN DEFAULT FALSE,
    pathLenConstraint INTEGER (0..MAX) OPTIONAL }] over [c[vs, ve)] as
    [(cA, pathLen)].  A pathLenConstraint needs cA and is at most 127. *)
let basic_constraints (c:B.bytes) (vs ve:nat) : option (bool & option nat) =
  match C.der_tlv c 0x30uy vs ve with
  | None -> None
  | Some (s, e) ->
    if e <> ve then None
    else
      let ca : option (bool & nat) =
        match C.der_tlv c 0x01uy s e with
        | Some (bs, be) ->
          if be = bs + 1 && byte_is c bs 0xFFuy then Some (true, be) else None
        | None -> Some (false, s) in
      match ca with
      | None -> None
      | Some (ca, p) ->
        if p = e then Some (ca, None)
        else
          match C.der_tlv c 0x02uy p e with
          | Some (is, ie) ->
            if ca && ie = e && ie = is + 1 && U8.v (Seq.index c is) < 0x80
            then Some (true, Some (U8.v (Seq.index c is)))
            else None
          | None -> None

(** The basicConstraints over [c[vs, ve)] make a CA that may have [below]
    intermediate certificates under it. *)
let ca_allows (c:B.bytes) (vs ve below:nat) : bool =
  match basic_constraints c vs ve with
  | Some (true, None) -> true
  | Some (true, Some n) -> below <= n
  | _ -> false

(** The first byte of [KeyUsage ::= BIT STRING] over [c[vs, ve)]: bit 0
    (digitalSignature) is [0x80], bit 5 (keyCertSign) is [0x04]. *)
let key_usage_bits (c:B.bytes) (vs ve:nat) : option U8.t =
  match C.der_tlv c 0x03uy vs ve with
  | None -> None
  | Some (s, e) ->
    if e <> ve || s >= e || U8.v (Seq.index c s) > 7 then None
    else if s + 1 = e then Some 0uy
    else Some (Seq.index c (s + 1))

let has_bit (b mask:U8.t) : bool = U8.logand b mask <> 0uy

(** The extensions over [c[xs, xe)] have no keyUsage, or one with a bit of
    [mask]. *)
let key_usage_allows (c:B.bytes) (xs xe:nat) (mask:U8.t) : bool =
  match find_extension c xs xe oid_key_usage with
  | None -> true
  | Some (vs, ve) ->
    (match key_usage_bits c vs ve with
     | Some b -> has_bit b mask
     | None -> false)

(** id-kp-serverAuth (1.3.6.1.5.5.7.3.1) at [c[s, e)]. *)
let is_server_auth (c:B.bytes) (s e:nat) : bool =
  e = s + 8 &&
  byte_is c s 0x2Buy && byte_is c (s + 1) 0x06uy && byte_is c (s + 2) 0x01uy &&
  byte_is c (s + 3) 0x05uy && byte_is c (s + 4) 0x05uy && byte_is c (s + 5) 0x07uy &&
  byte_is c (s + 6) 0x03uy && byte_is c (s + 7) 0x01uy

(** anyExtendedKeyUsage (2.5.29.37.0) at [c[s, e)]. *)
let is_any_eku (c:B.bytes) (s e:nat) : bool =
  e = s + 4 &&
  byte_is c s 0x55uy && byte_is c (s + 1) 0x1Duy && byte_is c (s + 2) 0x25uy &&
  byte_is c (s + 3) 0x00uy

(** Whether [found] or the OIDs over [c[pos, limit)] include serverAuth, if
    they are all well formed. *)
let rec eku_server_auth (c:B.bytes) (pos limit:nat) (found:bool)
  : Tot (option bool) (decreases (if limit > pos then limit - pos else 0)) =
  if pos >= limit then (if pos = limit then Some found else None)
  else
    match C.der_tlv c 0x06uy pos limit with
    | None -> None
    | Some (s, e) ->
      eku_server_auth c e limit (found || is_server_auth c s e || is_any_eku c s e)

(** [ExtKeyUsageSyntax ::= SEQUENCE SIZE (1..MAX) OF KeyPurposeId], if
    present among the extensions over [c[xs, xe)], allows TLS server
    authentication. *)
let ext_key_usage_ok (c:B.bytes) (xs xe:nat) : bool =
  match find_extension c xs xe oid_ext_key_usage with
  | None -> true
  | Some (vs, ve) ->
    (match C.der_tlv c 0x30uy vs ve with
     | Some (s, e) -> e = ve && eku_server_auth c s e false = Some true
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

let ip_is (c:B.bytes) (s e:nat) (a:ipv4) : bool =
  e = s + 4 &&
  byte_is c s a.ip0 && byte_is c (s + 1) a.ip1 && byte_is c (s + 2) a.ip2 &&
  byte_is c (s + 3) a.ip3

(** Whether [found] or a [GeneralName] over [c[pos, limit)] names the host:
    a dNSName ([2]) when [ip] is [None], an iPAddress ([7]) equal to [ip]
    otherwise. *)
let rec general_names_match (c:B.bytes) (pos limit:nat) (h:B.bytes) (ip:option ipv4)
  (found:bool)
  : Tot (option bool) (decreases (if limit > pos then limit - pos else 0)) =
  if pos >= limit then (if pos = limit then Some found else None)
  else
    match der_any c pos limit with
    | None -> None
    | Some (s, e) ->
      let tag = Seq.index c pos in
      let this =
        match ip with
        | Some a -> tag = 0x87uy && ip_is c s e a
        | None -> tag = 0x82uy && dns_matches c s e h in
      general_names_match c e limit h ip (found || this)

(** The subjectAltName among the extensions over [c[xs, xe)] names
    [hostname]. *)
let subject_alt_name_ok (c:B.bytes) (xs xe:nat) (hostname:B.bytes) : bool =
  match find_extension c xs xe oid_subject_alt_name with
  | None -> false
  | Some (vs, ve) ->
    (match C.der_tlv c 0x30uy vs ve with
     | Some (s, e) ->
       e = ve && B.length hostname > 0 &&
       general_names_match c s e hostname (ipv4_address hostname) false = Some true
     | None -> false)

(** {2 Certificates} *)

type tbs_fields = {
  version: nat;
  alg_s: nat;          (* signature AlgorithmIdentifier contents *)
  alg_e: nat;
  issuer_s: nat;       (* issuer Name, DER *)
  issuer_e: nat;
  not_before: nat;
  not_after: nat;
  subject_s: nat;      (* subject Name, DER *)
  subject_e: nat;
  ext_s: nat;          (* the extensions, empty if absent *)
  ext_e: nat;
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
  let exts : option (nat & nat) =
    if p = te then Some (te, te)
    else
      match C.der_tlv c 0xA3uy p te with
      | Some (xs, xe) ->
        if xe <> te || version <> 3 then None
        else
          (match C.der_tlv c 0x30uy xs xe with
           | Some (ls, le) ->
             if le <> xe || not (extensions_wf c ls le) then None else Some (ls, le)
           | None -> None)
      | None -> None in
  match exts with
  | None -> None
  | Some (ext_s, ext_e) ->
    Some {
      version;
      alg_s = a_s;
      alg_e = a_e;
      issuer_s = a_e;
      issuer_e = issuer_end;
      not_before;
      not_after;
      subject_s = ve;
      subject_e = subject_end;
      ext_s;
      ext_e;
    }

type parsed_certificate = {
  tbs_s: nat;          (* the signed TBSCertificate, DER *)
  tbs_e: nat;
  fields: tbs_fields;
  sig_alg_s: nat;      (* signatureAlgorithm contents *)
  sig_alg_e: nat;
  sig_s: nat;          (* signatureValue past the unused-bits byte *)
  sig_e: nat;
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
      tbs_s = cs;
      tbs_e = te;
      fields;
      sig_alg_s = a_s;
      sig_alg_e = a_e;
      sig_s = bs + 1;
      sig_e = be;
    }

(** {2 Signatures} *)

(** sha256/384/512WithRSAEncryption (1.2.840.113549.1.1.11/12/13) with NULL
    parameters (RFC 4055 5) at [c[s, e)]. *)
let sha_with_rsa (c:B.bytes) (s e:nat) (last:U8.t) : bool =
  e = s + 13 &&
  byte_is c s 0x06uy && byte_is c (s + 1) 0x09uy && byte_is c (s + 2) 0x2Auy &&
  byte_is c (s + 3) 0x86uy && byte_is c (s + 4) 0x48uy && byte_is c (s + 5) 0x86uy &&
  byte_is c (s + 6) 0xF7uy && byte_is c (s + 7) 0x0Duy && byte_is c (s + 8) 0x01uy &&
  byte_is c (s + 9) 0x01uy && byte_is c (s + 10) last && byte_is c (s + 11) 0x05uy &&
  byte_is c (s + 12) 0x00uy

(** ecdsa-with-SHA256 (1.2.840.10045.4.3.2) without parameters (RFC 5758
    3.2) at [c[s, e)]. *)
let ecdsa_with_sha256 (c:B.bytes) (s e:nat) : bool =
  e = s + 10 &&
  byte_is c s 0x06uy && byte_is c (s + 1) 0x08uy && byte_is c (s + 2) 0x2Auy &&
  byte_is c (s + 3) 0x86uy && byte_is c (s + 4) 0x48uy && byte_is c (s + 5) 0xCEuy &&
  byte_is c (s + 6) 0x3Duy && byte_is c (s + 7) 0x04uy && byte_is c (s + 8) 0x03uy &&
  byte_is c (s + 9) 0x02uy

(** The signature of certificate [child], parsed as [pc], verifies under
    the public key of certificate [issuer]. *)
let signed_by (child:certificate) (pc:parsed_certificate) (issuer:certificate) : GTot bool =
  let tbs = sub child pc.tbs_s pc.tbs_e in
  let sg = sub child pc.sig_s pc.sig_e in
  match C.certificate_raw_public_key issuer with
  | Some (C.RawRsa n e) ->
    if sha_with_rsa child pc.sig_alg_s pc.sig_alg_e 0x0Buy then
      C.rsa_pkcs1_verify C.Pkcs1Sha256 n e tbs sg
    else if sha_with_rsa child pc.sig_alg_s pc.sig_alg_e 0x0Cuy then
      C.rsa_pkcs1_verify C.Pkcs1Sha384 n e tbs sg
    else if sha_with_rsa child pc.sig_alg_s pc.sig_alg_e 0x0Duy then
      C.rsa_pkcs1_verify C.Pkcs1Sha512 n e tbs sg
    else false
  | Some (C.RawP256 q) ->
    ecdsa_with_sha256 child pc.sig_alg_s pc.sig_alg_e &&
    C.ecdsa_secp256r1_sha256_verify q tbs sg
  | None -> false

(** {2 Paths} *)

(** What every path certificate [c], parsed as [pc], satisfies at [t]
    seconds since 1970. *)
let path_certificate_ok (c:certificate) (pc:parsed_certificate) (t:nat) : bool =
  pc.fields.version = 3 &&
  range_eq c pc.sig_alg_s pc.sig_alg_e c pc.fields.alg_s pc.fields.alg_e &&
  pc.fields.not_before <= t + epoch_seconds && t + epoch_seconds <= pc.fields.not_after &&
  extensions_ok c pc.fields.ext_s pc.fields.ext_e &&
  ext_key_usage_ok c pc.fields.ext_s pc.fields.ext_e

(** What the leaf satisfies for [hostname]. *)
let leaf_ok (c:certificate) (pc:parsed_certificate) (hostname:B.bytes) : bool =
  subject_alt_name_ok c pc.fields.ext_s pc.fields.ext_e hostname &&
  key_usage_allows c pc.fields.ext_s pc.fields.ext_e 0x80uy

(** What a path certificate issuing others satisfies, with [below]
    intermediate certificates between it and the leaf. *)
let issuer_ok (c:certificate) (pc:parsed_certificate) (below:nat) : bool =
  (match find_extension c pc.fields.ext_s pc.fields.ext_e oid_basic_constraints with
   | Some (vs, ve) -> ca_allows c vs ve below
   | None -> false) &&
  key_usage_allows c pc.fields.ext_s pc.fields.ext_e 0x04uy

(** [a[pos ..]] is a concatenation of DER certificates. *)
let rec anchors_wf (a:B.bytes) (pos:nat)
  : Tot bool (decreases (if B.length a > pos then B.length a - pos else 0)) =
  pos >= B.length a ||
  (match C.der_tlv a 0x30uy pos (B.length a) with
   | None -> false
   | Some (_, e) -> anchors_wf a e)

(** [leaf] is one of the certificates over [a[pos ..]]. *)
let rec is_anchor (leaf:certificate) (a:B.bytes) (pos:nat)
  : Tot bool (decreases (if B.length a > pos then B.length a - pos else 0)) =
  pos < B.length a &&
  (match C.der_tlv a 0x30uy pos (B.length a) with
   | None -> false
   | Some (_, e) -> range_eq leaf 0 (B.length leaf) a pos e || is_anchor leaf a e)

(** Trust anchor [anc]'s subject is [child]'s issuer and its key signed
    [child]. *)
let anchor_issues (anc:certificate) (child:certificate) (pc:parsed_certificate) : GTot bool =
  match parse_certificate anc with
  | Some pa ->
    range_eq anc pa.fields.subject_s pa.fields.subject_e
      child pc.fields.issuer_s pc.fields.issuer_e &&
    signed_by child pc anc
  | None -> false

(** Some trust anchor over [a[pos ..]] issued [child]. *)
let rec anchored (a:B.bytes) (pos:nat) (child:certificate) (pc:parsed_certificate)
  : GTot bool (decreases (if B.length a > pos then B.length a - pos else 0)) =
  pos < B.length a &&
  (match C.der_tlv a 0x30uy pos (B.length a) with
   | None -> false
   | Some (_, e) -> anchor_issues (Seq.slice a pos e) child pc || anchored a e child pc)

(** [child], at [depth] in the path, chains to a trust anchor through a
    prefix of [rest]. *)
let rec chains (a:B.bytes) (t:nat) (child:certificate) (depth:nat) (rest:cert_chain)
  : GTot bool (decreases rest) =
  match parse_certificate child with
  | None -> false
  | Some pc ->
    anchored a 0 child pc ||
    (match rest with
     | [] -> false
     | next :: rest' ->
       (match parse_certificate next with
        | Some pn ->
          path_certificate_ok next pn t &&
          issuer_ok next pn depth &&
          range_eq child pc.fields.issuer_s pc.fields.issuer_e
            next pn.fields.subject_s pn.fields.subject_e &&
          signed_by child pc next &&
          chains a t next (depth + 1) rest'
        | None -> false))

[@@"opaque_to_smt"]
let validate_chain
  (hostname:T.hostname)
  (validation_time:validation_time)
  (trust_store:trust_store)
  (certs:cert_chain)
  : GTot (option peer_identity) =
  let t = validation_time.seconds_since_epoch in
  let a = trust_store.anchors in
  match certs with
  | leaf :: rest ->
    if not (anchors_wf a 0) then None
    else
      (match parse_certificate leaf with
       | Some pl ->
         if path_certificate_ok leaf pl t && leaf_ok leaf pl hostname &&
            (is_anchor leaf a 0 || chains a t leaf 0 rest)
         then Some {
           validated_hostname = hostname;
           leaf_public_key = leaf;
           permitted_signature_schemes = [];
         }
         else None
       | None -> None)
  | [] -> None
