module TLS13.X509.Spec.Def

(** The definition of [TLS13.X509.Spec.validate_chain]. *)

open TLS13.X509.Spec

val validate_chain_def
  (hostname:TLS13.Types.hostname)
  (validation_time:validation_time)
  (trust_store:trust_store)
  (certs:cert_chain)
  : Lemma (validate_chain hostname validation_time trust_store certs ==
           (match certs with
            | leaf :: _ ->
              if TLS13.X509.Chain.chain_ok hostname validation_time.seconds_since_epoch
                   trust_store.anchors certs
              then Some ({
                validated_hostname = hostname;
                leaf_public_key = leaf;
                permitted_signature_schemes = [];
              } <: peer_identity)
              else None
            | [] -> None))
