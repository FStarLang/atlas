module TLS13.X509.Spec

(** X.509 certificate path validation for TLS server authentication.

    [validate_chain] is RFC 5280 6.1 path validation and RFC 6125 name
    matching in a strict, fail-closed profile, over the certificates parsed
    with the verified DER parser everparse-asn1 generates from the RFC 5280
    profile [src/asn1/X509.asn]: it is defined in [TLS13.X509.Spec.fst] by
    [TLS13.X509.Chain.chain_ok], which documents the profile, and
    [TLS13.X509.Spec.Def] states that definition. *)

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

(** The peer identity the certificates [certs] establish for [hostname] at
    [validation_time]: its public key is the leaf certificate. *)
val validate_chain
  (hostname:T.hostname)
  (validation_time:validation_time)
  (trust_store:trust_store)
  (certs:cert_chain)
  : GTot (option peer_identity)
