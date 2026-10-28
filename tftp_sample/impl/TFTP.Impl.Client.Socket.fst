module TFTP.Impl.Client.Socket

(**
  Verified runner that drives the TFTP *client* (receiver) over a `Common.TCP`
  channel using the GENERIC verified loop `Common.ProtocolDriver.drive_steps`
  specialised to the committed instances
  `TFTP.Impl.Client.CanonicalProtocol.tftp_client_protocol_implementation`
  (the state-machine implementation dictionary) and
  `TFTP.Impl.Client.Endpoint.tftp_client_protocol_endpoint` (the scheduling +
  resource dictionary).

  `tftp_client_receive` is the C entry point: it allocates the endpoint's
  datagram / ACK / scratch buffers, runs the driver (one datagram per step),
  appends every accepted DATA payload to the caller's `outbuf`, frees
  everything it allocated and returns the number of bytes written.  The channel
  is left open (owned by the C glue).  The specification-only filename that
  seeds `Client_start` is an erased argument, so the endpoint config passed to
  `drive_steps` is built here and Custard specialises the driver to it.

  Custard extracts this module (the driver and both dictionaries are
  monomorphised); `run_tftp_client_connect` is a verified convenience wrapper
  that is not extracted.
**)

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module CPI  = Common.ProtocolImplementation
module PD   = Common.ProtocolDriver
module PE   = Common.ProtocolEndpoint
module SZ   = FStar.SizeT
module Seq  = FStar.Seq
module TCP  = Common.TCP
module U8   = FStar.UInt8
module U16  = FStar.UInt16
module Vec  = Pulse.Lib.Vec
module MR   = Pulse.Lib.MonotonicGhostRef

module TP   = TFTP.Protocol
module CC   = TFTP.Impl.Client.CanonicalProtocol
module EP   = TFTP.Impl.Client.Endpoint
module Log  = TFTP.Impl.Client.Log
module TW   = TFTP.Wire

#set-options "--fuel 1 --ifuel 1 --z3rlimit 10"

(* ───────────────────────────────────────────────────────────────────────────
   Impl-handle disposal: `Vec.free` the status cell, `drop_` the (affine) ghost
   progress reference.
   ─────────────────────────────────────────────────────────────────────────── *)

fn free_tftp_client
  (i:CC.tftp_client_impl)
  (#received:erased TCP.bytes)
  (#sent:erased TCP.bytes)
  (#st:erased TP.tftp_client_state)
requires
  CC.tftp_client_inv i received sent st **
  pure (Vec.is_full_vec i.CC.status)
ensures emp
{
  unfold (CC.tftp_client_inv i received sent st);
  with svs. _;
  Vec.free i.CC.status;
  drop_ (MR.pts_to i.CC.progress #1.0R (Log.mk_log received sent st))
}

(* ───────────────────────────────────────────────────────────────────────────
   The runner: drive the receiver over an already-connected channel.
   ─────────────────────────────────────────────────────────────────────────── *)

fn tftp_client_receive
  (ch:TCP.channel)
  (outbuf:array U8.t)
  (outcap:SZ.t)
  (fuel:SZ.t)
  (#filename:Ghost.erased TCP.bytes)
  (#o:Ghost.erased (Seq.seq U8.t))
requires
  TCP.is_channel ch Seq.empty Seq.empty **
  pts_to outbuf o **
  pure (Seq.length o == SZ.v outcap)
returns nbytes:SZ.t
ensures exists* (r s:TCP.bytes) (o1:Seq.seq U8.t).
  TCP.is_channel ch r s **
  pts_to outbuf o1 **
  pure (Seq.length o1 == SZ.v outcap /\ SZ.v nbytes <= SZ.v outcap)
{
  let cfg : EP.tftp_client_config = { EP.tcfg_filename = filename };

  (* 1. Fresh receiver handle (pi_invariant at the initial state). *)
  let i = CC.new_tftp_client ();

  (* 2. Allocate the endpoint's buffers as heap vecs and expose them as raw
        arrays for the endpoint frame.  The cursor stays a `Vec`. *)
  let dgram   = Vec.alloc 0uy 516sz;
  let ack     = Vec.alloc 0uy 4sz;
  let scratch = Vec.alloc 0uy 512sz;
  let cursor  = Vec.alloc 0sz 1sz;
  Vec.to_array_pts_to dgram;
  Vec.to_array_pts_to ack;
  Vec.to_array_pts_to scratch;

  let frame : EP.tftp_client_endpoint_frame = {
    EP.tef_dgram   = Vec.vec_to_array dgram;
    EP.tef_ack     = Vec.vec_to_array ack;
    EP.tef_scratch = Vec.vec_to_array scratch;
    EP.tef_out     = outbuf;
    EP.tef_outcap  = outcap;
    EP.tef_cursor  = cursor;
  };
  rewrite (pts_to (Vec.vec_to_array dgram) (Seq.create 516 0uy))
      as  (pts_to frame.EP.tef_dgram (Seq.create 516 0uy));
  rewrite (pts_to (Vec.vec_to_array ack) (Seq.create 4 0uy))
      as  (pts_to frame.EP.tef_ack (Seq.create 4 0uy));
  rewrite (pts_to (Vec.vec_to_array scratch) (Seq.create 512 0uy))
      as  (pts_to frame.EP.tef_scratch (Seq.create 512 0uy));
  rewrite (pts_to outbuf o) as (pts_to frame.EP.tef_out o);
  rewrite (Vec.pts_to cursor (Seq.create 1 0sz))
      as  (Vec.pts_to frame.EP.tef_cursor (Seq.create 1 0sz));

  (* 3. Fold the endpoint's persistent resources, then re-present them as the
        instance's projected slprops so unification pins `drive_steps`. *)
  fold (EP.tftp_client_payload_ready frame);
  fold (EP.tftp_client_frame_ready i cfg frame TP.tftp_client_initial);
  fold (EP.tftp_client_io_ready i ch frame Seq.empty Seq.empty TP.tftp_client_initial);

  rewrite (CC.tftp_client_inv i Seq.empty Seq.empty TP.tftp_client_initial)
      as  (CC.tftp_client_protocol_implementation.CPI.pi_invariant
            i Seq.empty Seq.empty TP.tftp_client_initial);
  rewrite (EP.tftp_client_frame_ready i cfg frame TP.tftp_client_initial)
      as  (EP.tftp_client_protocol_endpoint.PE.pe_frame_ready
            i cfg frame TP.tftp_client_initial);
  rewrite (EP.tftp_client_io_ready i ch frame Seq.empty Seq.empty TP.tftp_client_initial)
      as  (EP.tftp_client_protocol_endpoint.PE.pe_io_ready
            i ch frame Seq.empty Seq.empty TP.tftp_client_initial);

  (* 4. Run the GENERIC verified driver. *)
  let _res =
    PD.drive_steps
      #CC.tftp_client_impl
      #TP.tftp_client_state
      #TW.tftp_message
      #TP.tftp_client_local
      #unit
      #CC.tftp_client_protocol_implementation
      #EP.tftp_client_protocol_endpoint
      i cfg frame ch fuel
      (Ghost.hide #TCP.bytes Seq.empty)
      (Ghost.hide #TCP.bytes Seq.empty)
      (Ghost.hide TP.tftp_client_initial);
  with received1 sent1 st1. _;

  (* 5. Tear down: unfold, free what we allocated; the channel and `outbuf` go
        back to the caller. *)
  rewrite (EP.tftp_client_protocol_endpoint.PE.pe_frame_ready
            i cfg frame (Ghost.reveal st1))
      as  (EP.tftp_client_frame_ready i cfg frame (Ghost.reveal st1));
  rewrite (EP.tftp_client_protocol_endpoint.PE.pe_io_ready
            i ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1))
      as  (EP.tftp_client_io_ready
            i ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1));
  rewrite (CC.tftp_client_protocol_implementation.CPI.pi_invariant
            i (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1))
      as  (CC.tftp_client_inv
            i (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1));

  unfold (EP.tftp_client_frame_ready i cfg frame (Ghost.reveal st1));
  with sc_final. _;
  unfold (EP.tftp_client_io_ready
            i ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1));
  with raw_final dg_final ack_final. _;
  unfold (EP.tftp_client_payload_ready frame);
  with ob_final cv_final. _;

  let nbytes = Vec.op_Dot_Lparen_Rparen frame.EP.tef_cursor 0sz;

  rewrite (pts_to frame.EP.tef_scratch sc_final) as (pts_to (Vec.vec_to_array scratch) sc_final);
  Vec.to_vec_pts_to scratch;
  Vec.free scratch;
  rewrite (pts_to frame.EP.tef_dgram dg_final) as (pts_to (Vec.vec_to_array dgram) dg_final);
  Vec.to_vec_pts_to dgram;
  Vec.free dgram;
  rewrite (pts_to frame.EP.tef_ack ack_final) as (pts_to (Vec.vec_to_array ack) ack_final);
  Vec.to_vec_pts_to ack;
  Vec.free ack;
  rewrite (Vec.pts_to frame.EP.tef_cursor cv_final) as (Vec.pts_to cursor cv_final);
  Vec.free cursor;
  rewrite (pts_to frame.EP.tef_out ob_final) as (pts_to outbuf ob_final);

  free_tftp_client i #received1 #sent1 #st1;
  nbytes
}

(* ───────────────────────────────────────────────────────────────────────────
   Connect-style entry: connect, receive into `outbuf`, close.
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
fn run_tftp_client_connect
  (host:array U8.t)
  (host_len:SZ.t)
  (port:U16.t)
  (outbuf:array U8.t)
  (outcap:SZ.t)
  (fuel:SZ.t)
  (#filename:Ghost.erased TCP.bytes)
requires
  pts_to host 'h **
  pts_to outbuf 'o **
  pure (Seq.length 'h == SZ.v host_len /\ Seq.length 'o == SZ.v outcap)
ensures
  pts_to host 'h **
  (exists* (o1:Seq.seq U8.t). pts_to outbuf o1)
{
  match TCP.connect_tcp host host_len port {
    Some ch -> {
      assert (pure (Seq.equal (Seq.create 0 0uy) (Seq.empty #U8.t)));
      rewrite (TCP.is_channel ch (Seq.create 0 0uy) (Seq.create 0 0uy))
          as  (TCP.is_channel ch Seq.empty Seq.empty);
      let _n = tftp_client_receive ch outbuf outcap fuel #filename;
      TCP.close ch
    }
    None -> {
      ()
    }
  }
}
