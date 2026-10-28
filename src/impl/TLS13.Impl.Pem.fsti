module TLS13.Impl.Pem

(** The PEM front end the C runtime uses to turn host-supplied credentials
    into the DER the verified client and server consume, implementing
    [TLS13.Pem.Spec].

    The caller supplies the output buffer, as long as the input: decoding
    never produces more bytes than it consumes, so the result always fits.
    The functions do not allocate. *)

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module S = TLS13.Pem.Spec
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8

(** [r] reports [spec]: [None] for a rejected input, and otherwise the length
    of the result, which is the prefix of [out]. *)
let decoded_into (spec:option B.bytes) (out:B.bytes) (r:option SZ.t) : prop =
  match spec, r with
  | None, None -> True
  | Some d, Some n -> SZ.v n <= Seq.length out /\ Seq.slice out 0 (SZ.v n) == d
  | _ -> False

(** [S.certificates_to_der]: the concatenated DER of every CERTIFICATE block
    of the PEM bundle [pem]. *)
fn certificates_to_der
  (pem:array U8.t)
  (pem_len:SZ.t)
  (out:array U8.t)
  requires pts_to pem 'pem_bytes **
           pts_to out 'out_bytes **
           pure (Seq.length 'pem_bytes == SZ.v pem_len /\
                 Seq.length 'out_bytes == SZ.v pem_len)
  returns r:option SZ.t
  ensures exists* out_bytes.
          pts_to pem 'pem_bytes **
          pts_to out out_bytes **
          pure (Seq.length out_bytes == SZ.v pem_len /\
                decoded_into (S.certificates_to_der 'pem_bytes) out_bytes r)

(** [S.private_key_to_der]: a DER private key, given as DER or as the first
    PEM private-key block of [key]. *)
fn private_key_to_der
  (key:array U8.t)
  (key_len:SZ.t)
  (out:array U8.t)
  requires pts_to key 'key_bytes **
           pts_to out 'out_bytes **
           pure (Seq.length 'key_bytes == SZ.v key_len /\
                 Seq.length 'out_bytes == SZ.v key_len)
  returns r:option SZ.t
  ensures exists* out_bytes.
          pts_to key 'key_bytes **
          pts_to out out_bytes **
          pure (Seq.length out_bytes == SZ.v key_len /\
                decoded_into (S.private_key_to_der 'key_bytes) out_bytes r)
