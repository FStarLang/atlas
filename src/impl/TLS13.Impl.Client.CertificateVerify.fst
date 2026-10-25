module TLS13.Impl.Client.CertificateVerify

(** The client's check of the server's CertificateVerify signature.

    The public key is read out of the leaf certificate by the OpenSSL TCB
    ([TLS13.OpenSSL.certificate_raw_public_key], specified by the assumed
    [TLS13.Crypto.Spec.certificate_raw_public_key]); the signature itself is
    checked by the verified hacl-pulse verifiers in [TLS13.Crypto], against
    [TLS13.Crypto.Spec.verify_signature]. *)

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CL = TLS13.ConnectionLog
module Cr = TLS13.Crypto
module L = TLS13.Impl.Messages
module O = TLS13.OpenSSL
module SZ = FStar.SizeT
module T = TLS13.Types
module U16 = FStar.UInt16
module U8 = FStar.UInt8

(* Large enough for any modulus [C.rsa_modulus_ok] accepts. *)
inline_for_extraction noextract
let raw_key_capacity : SZ.t = 1024sz

fn verify_peer_signature
  (certificate:array U8.t)
  (certificate_len:SZ.t)
  (scheme:U16.t)
  (sch:erased T.signature_scheme)
  (input:array U8.t)
  (input_len:SZ.t)
  (sg:array U8.t)
  (sg_len:SZ.t)
  requires pts_to certificate 'certificate_bytes **
           pts_to input 'input_bytes **
           pts_to sg 'sg_bytes **
           pure (SZ.v certificate_len <= B.length 'certificate_bytes /\
                 SZ.v input_len <= B.length 'input_bytes /\
                 SZ.v sg_len <= B.length 'sg_bytes /\
                 L.signature_scheme_matches scheme sch)
  returns ok:bool
  ensures pts_to certificate 'certificate_bytes **
          pts_to input 'input_bytes **
          pts_to sg 'sg_bytes **
          pure (ok ==>
                C.verify_signature (reveal sch)
                  (CL.raw_slice 'certificate_bytes 0 (SZ.v certificate_len))
                  (CL.raw_slice 'input_bytes 0 (SZ.v input_len))
                  (CL.raw_slice 'sg_bytes 0 (SZ.v sg_len)) == true)
{
  let mut key = [| 0uy; raw_key_capacity |];
  let mut exponent = [| 0uy; raw_key_capacity |];
  let mut lens = [| 0sz; 2sz |];
  let kind =
    O.certificate_raw_public_key
      certificate certificate_len key raw_key_capacity exponent raw_key_capacity lens;
  C.lemma_verify_signature_def (reveal sch)
    (CL.raw_slice 'certificate_bytes 0 (SZ.v certificate_len))
    (CL.raw_slice 'input_bytes 0 (SZ.v input_len))
    (CL.raw_slice 'sg_bytes 0 (SZ.v sg_len));
  if (scheme = 0x0804us && kind = 1uy) {
    let modulus_len = lens.(0sz);
    let exponent_len = lens.(1sz);
    Cr.verify_rsa_pss_rsae_sha256
      key modulus_len exponent exponent_len input input_len sg sg_len
  } else if (scheme = 0x0403us && kind = 2uy) {
    let point_len = lens.(0sz);
    Cr.verify_ecdsa_secp256r1_sha256 key point_len input input_len sg sg_len
  } else {
    false
  }
}
