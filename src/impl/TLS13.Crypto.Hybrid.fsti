module TLS13.Crypto.Hybrid

#lang-pulse

(**
  Pulse bindings for the X25519MLKEM768 hybrid key agreement of RFC 10024,
  implemented by calling hacl-pulse's verified ML-KEM-768 and X25519, and
  specified by [TLS13.Crypto.Hybrid.Spec].

  Like the single-group bindings in [TLS13.Crypto], each function takes
  exact-width buffers and performs no group dispatch; agility over the
  negotiated group belongs to [TLS13.KEX].
**)

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module H = TLS13.Crypto.Hybrid.Spec
module U8 = FStar.UInt8

(** The client's 1216-byte key share from its 96-byte private seeds. *)
fn x25519mlkem768_client_public (sk: array U8.t) (out: array U8.t)
  requires pts_to sk 'sk_bytes **
           pts_to out 'old **
           pure (B.length 'sk_bytes == 96 /\ B.length 'old == 1216)
  ensures pts_to sk 'sk_bytes **
          pts_to out (H.x25519mlkem768_client_public 'sk_bytes)

(** The server's side: check the client's 1216-byte share, encapsulate to it,
    and produce the server's 1120-byte share and the 64-byte shared secret.
    [false] exactly when the model rejects (illegal_parameter): a bad ML-KEM
    encapsulation key or an all-zero X25519 output. *)
fn x25519mlkem768_server_encaps
  (sk: array U8.t)
  (client_share: array U8.t)
  (share_out: array U8.t)
  (ss_out: array U8.t)
  requires pts_to sk 'sk_bytes **
           pts_to client_share 'cs_bytes **
           pts_to share_out 'old_share **
           pts_to ss_out 'old_ss **
           pure (B.length 'sk_bytes == 64 /\
                 B.length 'cs_bytes == 1216 /\
                 B.length 'old_share == 1120 /\
                 B.length 'old_ss == 64)
  returns ok: bool
  ensures exists* share ss.
          pts_to sk 'sk_bytes **
          pts_to client_share 'cs_bytes **
          pts_to share_out share **
          pts_to ss_out ss **
          pure (B.length share == 1120 /\
                B.length ss == 64 /\
                (ok <==> Some? (H.x25519mlkem768_server_shared 'sk_bytes 'cs_bytes)) /\
                (ok ==>
                  Some? (H.x25519mlkem768_server_share 'sk_bytes 'cs_bytes) /\
                  share == Some?.v (H.x25519mlkem768_server_share 'sk_bytes 'cs_bytes) /\
                  ss == Some?.v (H.x25519mlkem768_server_shared 'sk_bytes 'cs_bytes)))

(** The client's side: decapsulate the server's 1120-byte share into the
    64-byte shared secret.  [false] exactly when the model rejects: an
    all-zero X25519 output. *)
fn x25519mlkem768_client_shared
  (sk: array U8.t)
  (server_share: array U8.t)
  (ss_out: array U8.t)
  requires pts_to sk 'sk_bytes **
           pts_to server_share 'ss_bytes **
           pts_to ss_out 'old **
           pure (B.length 'sk_bytes == 96 /\
                 B.length 'ss_bytes == 1120 /\
                 B.length 'old == 64)
  returns ok: bool
  ensures exists* ss.
          pts_to sk 'sk_bytes **
          pts_to server_share 'ss_bytes **
          pts_to ss_out ss **
          pure (B.length ss == 64 /\
                (ok <==> Some? (H.x25519mlkem768_client_shared 'sk_bytes 'ss_bytes)) /\
                (ok ==> ss == Some?.v (H.x25519mlkem768_client_shared 'sk_bytes 'ss_bytes)))
