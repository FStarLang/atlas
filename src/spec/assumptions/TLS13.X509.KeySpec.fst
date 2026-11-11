module TLS13.X509.KeySpec

(** The public key of a certificate, read with the verified DER parser
    everparse-asn1 generates from the RFC 5280 profile [src/asn1/X509.asn]
    ([TLS13.X509.Profile]).  This is the definition of
    [TLS13.Crypto.Spec.certificate_raw_public_key]. *)

open TLS13.Crypto.RawKey

module B = TLS13.Bytes
module Seq = FStar.Seq
module U8 = FStar.UInt8
module XP = TLS13.X509.Profile
module XG = TLS13.Wire.Generated.X509

(** [b] is the byte string [l]. *)
let bytes_is (b:B.bytes) (l:list U8.t) : bool = Seq.eq b (Seq.seq_of_list l)

(** The content octets of OBJECT IDENTIFIER [o] are [l]. *)
let oid_is (o:ASN1.Base.asn1_oid_t) (l:list U8.t) : bool =
  bytes_is (ASN1.Spec.Content.Enc.leaf_enc ASN1.Base.ASN1_OID o) l

(** The [AlgorithmIdentifier] parameters are present and DER-encode as [l]. *)
let params_are (p:option ASN1.Base.asn1_value) (l:list U8.t) : bool =
  match p with
  | Some v -> bytes_is (ASN1.Spec.Value.Enc.asn1_value_enc v) l
  | None -> false

(** [rsaEncryption] (1.2.840.113549.1.1.1) with NULL parameters (RFC 3279
    2.3.1), and [id-ecPublicKey] (1.2.840.10045.2.1) on the named curve
    [prime256v1] (1.2.840.10045.3.1.7) or [secp384r1] (1.3.132.0.34) (RFC 5480
    2.1.1). *)
let rsa_encryption_oid : list U8.t =
  [0x2Auy; 0x86uy; 0x48uy; 0x86uy; 0xF7uy; 0x0Duy; 0x01uy; 0x01uy; 0x01uy]
let der_null : list U8.t = [0x05uy; 0x00uy]
let ec_public_key_oid : list U8.t =
  [0x2Auy; 0x86uy; 0x48uy; 0xCEuy; 0x3Duy; 0x02uy; 0x01uy]
let prime256v1_param : list U8.t =
  [0x06uy; 0x08uy; 0x2Auy; 0x86uy; 0x48uy; 0xCEuy; 0x3Duy; 0x03uy; 0x01uy; 0x07uy]
let secp384r1_param : list U8.t =
  [0x06uy; 0x05uy; 0x2Buy; 0x81uy; 0x04uy; 0x00uy; 0x22uy]

(** The magnitude of a non-negative INTEGER from its content octets: without
    the sign octet, if it has one. *)
let uint_magnitude (b:B.bytes) : option B.bytes =
  if Seq.length b = 0 || U8.v (Seq.index b 0) >= 0x80 then None
  else if Seq.index b 0 = 0uy && Seq.length b > 1 then Some (Seq.slice b 1 (Seq.length b))
  else Some b

let int_bytes (x:ASN1.Base.asn1_integer_t ASN1.Base.asn1_any_integer_bound) : B.bytes =
  ASN1.Spec.Content.Enc.integer_enc ASN1.Base.asn1_any_integer_bound x

(** The modulus and public exponent of [RSAPublicKey ::= SEQUENCE { INTEGER,
    INTEGER }] (RFC 8017 A.1.1), as magnitudes. *)
let rsa_raw (k:ASN1.Base.asn1_t XG.k_RSAPublicKey) : option raw_public_key =
  match uint_magnitude (int_bytes (fst k)), uint_magnitude (int_bytes (snd k)) with
  | Some n, Some e -> Some (RawRsa n e)
  | _ -> None

(** The [x || y] of an uncompressed point (SEC 1 2.3.3) with [n]-byte [x || y]. *)
let ec_point (b:B.bytes) (n:nat) : option B.bytes =
  if Seq.length b = n + 1 && Seq.index b 0 = 0x04uy then Some (Seq.slice b 1 (n + 1)) else None

(** The raw key of a [SubjectPublicKeyInfo], whose BIT STRING must have no
    unused bits: for [rsaEncryption], it holds the DER [RSAPublicKey]. *)
let spki_raw_public_key (s:XP.spki) : GTot (option raw_public_key) =
  let a = XP.spki_alg s in
  let u = ASN1.Base.BYTES_WITH_UNUSEDBITS?.unused (XP.spki_key s) in
  let b = ASN1.Base.BYTES_WITH_UNUSEDBITS?.b (XP.spki_key s) in
  if u <> 0uy then None
  else if oid_is (XP.alg_oid a) rsa_encryption_oid && params_are (XP.alg_params a) der_null then
    (match XP.parse_full XG.k_RSAPublicKey b with
     | Some k -> rsa_raw k
     | None -> None)
  else if oid_is (XP.alg_oid a) ec_public_key_oid && params_are (XP.alg_params a) prime256v1_param then
    (match ec_point b 64 with Some p -> Some (RawP256 p) | None -> None)
  else if oid_is (XP.alg_oid a) ec_public_key_oid && params_are (XP.alg_params a) secp384r1_param then
    (match ec_point b 96 with Some p -> Some (RawP384 p) | None -> None)
  else None

(** The [rsaEncryption], P-256 or P-384 public key of a DER certificate: the
    certificate's DER encoding must be the whole input. *)
let certificate_key (certificate:B.bytes) : GTot (option raw_public_key) =
  match XP.parse_full XG.k_Certificate certificate with
  | Some v -> spki_raw_public_key (XP.tbs_spki (XP.cert_tbs v))
  | None -> None
