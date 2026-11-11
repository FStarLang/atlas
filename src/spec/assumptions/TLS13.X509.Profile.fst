module TLS13.X509.Profile

(** The certificates this library accepts, as ASN.1 values.

    [src/asn1/X509.asn] is the RFC 5280 profile: everparse-asn1 generates from
    it the specification [TLS13.Wire.Generated.X509] (an [asn1_k] description
    of each type, whose values are [asn1_t k] and whose DER parser is
    [ASN1.Spec.Interpreter.asn1_as_parser k]) and the verified Pulse
    validators and parsers in [TLS13.Wire.Generated.X509.Impl].  This module
    names the fields of those values that the TLS specifications read. *)

open ASN1.Base
module X = TLS13.Wire.Generated.X509
module I = ASN1.Spec.Interpreter
module LP = LowParse.Spec.Base
module Ser = ASN1.Spec.Serializer
module U8 = FStar.UInt8

type certificate = asn1_t X.k_Certificate
type tbs = asn1_t X.k_TBSCertificate
type alg_id = asn1_t X.k_AlgorithmIdentifier
type spki = asn1_t X.k_SubjectPublicKeyInfo
type name = asn1_t X.k_Name
type extension = asn1_t X.k_Extension

(** The value of type [k] whose DER encoding is exactly [c]. *)
let parse_full (#s:_) (k: asn1_k s) (c: Seq.seq U8.t) : GTot (option (asn1_t k)) =
  match LP.parse (I.asn1_as_parser k) c with
  | Some (v, n) -> if n = Seq.length c then Some v else None
  | None -> None

(** {2 Field projections} (the order of [src/asn1/X509.asn]) *)

let cert_tbs (c: certificate) : tbs = fst c
let cert_sig_alg (c: certificate) : alg_id = fst (snd c)
let cert_sig (c: certificate) : asn1_bitstring_t = snd (snd c)

let tbs_version (t: tbs) = fst t
let tbs_sig_alg (t: tbs) : alg_id = fst (snd (snd t))
let tbs_issuer (t: tbs) : name = fst (snd (snd (snd t)))
let tbs_validity (t: tbs) : asn1_t X.k_Validity = fst (snd (snd (snd (snd t))))
let tbs_subject (t: tbs) : name = fst (snd (snd (snd (snd (snd t)))))
let tbs_spki (t: tbs) : spki = fst (snd (snd (snd (snd (snd (snd t))))))
let tbs_extensions (t: tbs) : option (sized_list true extension) = snd (snd (snd (snd (snd (snd (snd (snd (snd t))))))))

let alg_oid (a: alg_id) : asn1_oid_t = fst a
let alg_params (a: alg_id) : option asn1_value = snd a
let spki_alg (s: spki) : alg_id = fst s
let spki_key (s: spki) : asn1_bitstring_t = snd s

let ext_oid (e: extension) : asn1_oid_t = fst e
let ext_critical (e: extension) : bool = v_of_default (fst (snd e))
let ext_value (e: extension) : Seq.seq U8.t = snd (snd e)
