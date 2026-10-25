module TLS13.Impl.ServerCredentials

(** The server's credential: its certificate and private key, and the
    CertificateVerify signatures made with it.

    The certificate is the DER leaf the server sends, and also the
    credential's identity: [C.credential_signature_scheme] and
    [C.verify_signature] read its public key with the verified parser
    [C.certificate_raw_public_key].  The private key is a DER PKCS#8
    [PrivateKeyInfo], PKCS#1 [RSAPrivateKey] or SEC1 [ECPrivateKey] for an RSA
    or P-256 certificate key.  Signing is hacl-pulse's RSASSA-PSS or ECDSA,
    with salt and nonce from [TLS13.Crypto.random_bytes], and every signature
    is checked with the verified verifier against the certificate before it is
    returned -- which is what establishes [sign_certificate_verify]'s
    postcondition, and also rejects a private key that does not match the
    certificate. *)

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CS = TLS13.Spec.StateMachine
module Seq = FStar.Seq
module SZ = FStar.SizeT
module T = TLS13.Types
module U16 = FStar.UInt16
module U8 = FStar.UInt8

val server_credentials : Type0

val is_server_credentials:
  server_credentials ->
  certificate_chain:B.bytes ->
  credential_identity:CS.server_credential_identity ->
  slprop

fn server_credentials_new
  (certificate_chain:array U8.t)
  (certificate_chain_len:SZ.t)
  (private_key:array U8.t)
  (private_key_len:SZ.t)
  requires pts_to certificate_chain 'certificate_chain_bytes **
           pts_to private_key 'private_key_bytes **
           pure (B.length 'certificate_chain_bytes == SZ.v certificate_chain_len /\
                 B.length 'private_key_bytes == SZ.v private_key_len)
  returns result: option server_credentials
  ensures exists* credential_identity.
          pts_to certificate_chain 'certificate_chain_bytes **
          pts_to private_key 'private_key_bytes **
          (match result with
           | Some creds ->
             is_server_credentials
               creds
               (Ghost.reveal 'certificate_chain_bytes)
               credential_identity
           | None -> emp)

fn server_credentials_clone (creds:server_credentials)
  requires is_server_credentials creds 'certificate_chain 'credential_identity
  returns clone: server_credentials
  ensures is_server_credentials creds 'certificate_chain 'credential_identity **
          is_server_credentials clone 'certificate_chain 'credential_identity

fn sign_certificate_verify
  (creds:server_credentials)
  (input:array U8.t)
  (input_len:SZ.t)
  (signature:array U8.t)
  (signature_capacity:SZ.t)
  requires is_server_credentials creds 'certificate_chain 'credential_identity **
           pts_to input 'input_bytes **
           pts_to signature 'old_signature **
           pure (SZ.v input_len <= B.length 'input_bytes /\
                 B.length 'old_signature == SZ.v signature_capacity)
  returns result: option SZ.t
  ensures exists* signature_bytes.
          is_server_credentials creds 'certificate_chain 'credential_identity **
          pts_to input 'input_bytes **
          pts_to signature signature_bytes **
          pure (SZ.v input_len <= B.length (Ghost.reveal 'input_bytes) /\
                B.length signature_bytes == SZ.v signature_capacity /\
                (match result with
                 | Some signature_len ->
                   SZ.v signature_len <= SZ.v signature_capacity /\
                   SZ.v signature_len <= B.length signature_bytes /\
                   C.verify_signature
                     (C.credential_signature_scheme
                       (Ghost.reveal 'credential_identity))
                     (Ghost.reveal 'credential_identity)
                     (Seq.slice (Ghost.reveal 'input_bytes) 0 (SZ.v input_len))
                     (Seq.slice signature_bytes 0 (SZ.v signature_len))
                 | None -> True))

(* The wire code of the scheme the credential can produce (parity gap G5).
   TLS 1.3 fixes a credential's algorithm by its SubjectPublicKeyInfo, so this
   is a pure query of the loaded key: 0x0804 for an RSA key, 0x0403 for a P-256
   key.  It is what lets the server's selection and its CertificateVerify
   follow the credential instead of being pinned to rsa_pss_rsae_sha256. *)
fn server_credential_signature_scheme (creds:server_credentials)
  requires is_server_credentials creds 'certificate_chain 'credential_identity
  returns code: U16.t
  ensures is_server_credentials creds 'certificate_chain 'credential_identity **
          pure ((U16.v code == 0x0804 /\
                 C.credential_signature_scheme
                   (Ghost.reveal 'credential_identity) ==
                   T.Rsa_pss_rsae_sha256) \/
                (U16.v code == 0x0403 /\
                 C.credential_signature_scheme
                   (Ghost.reveal 'credential_identity) ==
                   T.Ecdsa_secp256r1_sha256))

fn copy_server_certificate_chain
  (creds:server_credentials)
  (out:array U8.t)
  (out_capacity:SZ.t)
  requires is_server_credentials creds 'certificate_chain 'credential_identity **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_capacity)
  returns result: option SZ.t
  ensures exists* out_bytes.
          is_server_credentials creds 'certificate_chain 'credential_identity **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_capacity /\
                (match result with
                 | Some written ->
                  SZ.v written == B.length (Ghost.reveal 'certificate_chain) /\
                  SZ.v written <= SZ.v out_capacity /\
                  Seq.equal
                    (Seq.slice out_bytes 0 (SZ.v written))
                    (Ghost.reveal 'certificate_chain)
                 | None ->
                   B.length (Ghost.reveal 'certificate_chain) > SZ.v out_capacity))

fn server_credentials_free (creds:server_credentials)
  requires is_server_credentials creds 'certificate_chain 'credential_identity
  ensures emp
