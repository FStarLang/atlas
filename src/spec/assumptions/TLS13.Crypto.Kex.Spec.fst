module TLS13.Crypto.Kex.Spec

module C = TLS13.Crypto.Spec
module H = TLS13.Crypto.Hybrid.Spec

let lemma_kex_agreement g csk ssk =
  match g with
  | C.KexX25519 | C.KexP256 ->
    C.lemma_kex_shared_agreement g csk ssk
      (C.kex_public_from_private g csk) (C.kex_public_from_private g ssk)
  | C.KexX25519MLKEM768 ->
    H.lemma_x25519mlkem768_agreement csk ssk
