module TLS13.Impl.Server.Material

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module SZ = FStar.SizeT
module U8 = FStar.UInt8

fn copy_server_random_and_private_from_payload
  (payload:array U8.t)
  (server_random:array U8.t)
  (server_private_key:array U8.t)
  requires pts_to payload 'payload_bytes **
           pts_to server_random 'old_server_random **
           pts_to server_private_key 'old_server_private_key **
           pure (B.length 'payload_bytes == 128 /\
                 B.length 'old_server_random == 32 /\
                 B.length 'old_server_private_key == 32)
  ensures pts_to payload 'payload_bytes **
          pts_to server_random (CL.raw_slice 'payload_bytes 0 32) **
          pts_to server_private_key (CL.raw_slice 'payload_bytes 32 64) **
          pure (B.length (CL.raw_slice 'payload_bytes 0 32) == 32 /\
                B.length (CL.raw_slice 'payload_bytes 32 64) == 32)

(* RFC 10024: the X25519MLKEM768 server randomness is payload[64,128). *)
fn copy_server_random_and_hybrid_private_from_payload
  (payload:array U8.t)
  (server_random:array U8.t)
  (server_hybrid_private:array U8.t)
  requires pts_to payload 'payload_bytes **
           pts_to server_random 'old_server_random **
           pts_to server_hybrid_private 'old_server_hybrid_private **
           pure (B.length 'payload_bytes == 128 /\
                 B.length 'old_server_random == 32 /\
                 B.length 'old_server_hybrid_private == 64)
  ensures pts_to payload 'payload_bytes **
          pts_to server_random (CL.raw_slice 'payload_bytes 0 32) **
          pts_to server_hybrid_private (CL.raw_slice 'payload_bytes 64 128) **
          pure (B.length (CL.raw_slice 'payload_bytes 0 32) == 32 /\
                B.length (CL.raw_slice 'payload_bytes 64 128) == 64)
