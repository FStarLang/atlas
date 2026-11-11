module TLS13.X509.KeySpec.Def

(** [TLS13.Crypto.Spec.certificate_raw_public_key] is
    [TLS13.X509.KeySpec.certificate_key]. *)

val certificate_raw_public_key_def (certificate:TLS13.Crypto.Spec.public_key)
  : Lemma (TLS13.Crypto.Spec.certificate_raw_public_key certificate ==
           TLS13.X509.KeySpec.certificate_key certificate)
