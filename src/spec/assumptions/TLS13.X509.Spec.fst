module TLS13.X509.Spec

let validate_chain hostname validation_time trust_store certs =
  match certs with
  | leaf :: _ ->
    if TLS13.X509.Chain.chain_ok hostname validation_time.seconds_since_epoch
         trust_store.anchors certs
    then Some {
      validated_hostname = hostname;
      leaf_public_key = leaf;
      permitted_signature_schemes = [];
    }
    else None
  | [] -> None
