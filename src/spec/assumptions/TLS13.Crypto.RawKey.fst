module TLS13.Crypto.RawKey

module B = TLS13.Bytes

(** A SubjectPublicKeyInfo in the raw form the hacl-pulse verifiers consume:
    an [rsaEncryption] key as its big-endian modulus and public exponent, or
    a P-256 or P-384 key as its 64- or 96-byte affine point [x || y]. *)
type raw_public_key =
  | RawRsa : modulus:B.bytes -> exponent:B.bytes -> raw_public_key
  | RawP256 : point:B.bytes -> raw_public_key
  | RawP384 : point:B.bytes -> raw_public_key
