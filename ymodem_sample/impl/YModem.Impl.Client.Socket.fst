module YModem.Impl.Client.Socket

(**
  Verified runner that drives the YMODEM *client* (receiver) over a
  `Common.TCP` channel using the GENERIC verified loop
  `Common.ProtocolDriver.drive_steps` specialised to the committed instances
  `YModem.Impl.Client.CanonicalProtocol.ymodem_client_protocol_implementation`
  (the state-machine implementation dictionary) and
  `YModem.Impl.Client.Endpoint.ymodem_client_protocol_endpoint` (the scheduling
  + resource dictionary).

  `ymodem_client_receive` is the C entry point: it allocates the endpoint's
  scratch buffers, runs the driver, appends every accepted data-block payload to
  the caller's `outbuf`, frees everything it allocated and returns the number of
  bytes written.  The channel is left open (the C glue still speaks the YMODEM
  end-of-batch exchange on it).  The specification-only filename/length that
  seed `Client_start` are erased arguments, so the endpoint config passed to
  `drive_steps` is built here and Custard specialises the driver to it.

  Custard extracts this module (the driver and both dictionaries are
  monomorphised); `run_ymodem_client_connect` is a verified convenience wrapper
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

module YP   = YModem.Protocol
module CC   = YModem.Impl.Client.CanonicalProtocol
module EP   = YModem.Impl.Client.Endpoint
module Log  = YModem.Impl.Client.Log
module YMsg = YModem.Wire.Generated.Ymodem_message

#set-options "--fuel 1 --ifuel 1 --z3rlimit 10"

(* ───────────────────────────────────────────────────────────────────────────
   Impl-handle disposal (mirror of calc's `free_canonical_server`)

   `new_ymodem_client` exposes `pure (Vec.is_full_vec i.status)`; the caller
   threads that pure fact here to `Vec.free` the concrete single-cell status
   vector.  The monotonic ghost progress reference is affine and disposed with
   `drop_` (the only resource dropped — everything concrete is freed).
   ─────────────────────────────────────────────────────────────────────────── *)

fn free_ymodem_client
  (i:CC.ymodem_client_impl)
  (#received:erased TCP.bytes)
  (#sent:erased TCP.bytes)
  (#st:erased YP.ymodem_client_state)
requires
  CC.ymodem_client_inv i received sent st **
  pure (Vec.is_full_vec i.status)
ensures emp
{
  unfold (CC.ymodem_client_inv i received sent st);
  with svs. _;
  Vec.free i.CC.status;
  drop_ (MR.pts_to i.CC.progress #1.0R (Log.mk_log received sent st))
}

(* ───────────────────────────────────────────────────────────────────────────
   The runner: drive the receiver over an already-connected channel.
   ─────────────────────────────────────────────────────────────────────────── *)

fn ymodem_client_receive
  (ch:TCP.channel)
  (outbuf:array U8.t)
  (outcap:SZ.t)
  (fuel:SZ.t)
  (#filename:Ghost.erased TCP.bytes)
  (#len:Ghost.erased nat)
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
  let cfg : EP.ymodem_client_config = { EP.ycfg_filename = filename; EP.ycfg_len = len };

  (* 1. Fresh receiver handle: pi_invariant at the initial state, plus the pure
        `is_full_vec i.status` witness we need to free it later. *)
  let i = CC.new_ymodem_client ();

  (* 2. Allocate the four persistent transport buffers as heap vecs, then expose
        their contents as raw-array points-to so they can populate the endpoint
        frame (whose fields are `array U8.t`).  The cursor stays a `Vec`. *)
  let ctrl = Vec.alloc 0uy 1sz;
  let soh  = Vec.alloc 0uy 133sz;
  let ack  = Vec.alloc 0uy 1sz;
  let ycnf = Vec.alloc 0uy 128sz;
  let cursor = Vec.alloc 0sz 1sz;
  Vec.to_array_pts_to ctrl;
  Vec.to_array_pts_to soh;
  Vec.to_array_pts_to ack;
  Vec.to_array_pts_to ycnf;

  let frame : EP.ymodem_client_endpoint_frame = {
    EP.yef_ctrl = Vec.vec_to_array ctrl;
    EP.yef_soh  = Vec.vec_to_array soh;
    EP.yef_ack  = Vec.vec_to_array ack;
    EP.yef_ycnf = Vec.vec_to_array ycnf;
    EP.yef_out  = outbuf;
    EP.yef_outcap = outcap;
    EP.yef_cursor = cursor;
  };
  rewrite (pts_to (Vec.vec_to_array ctrl) (Seq.create 1 0uy))
      as  (pts_to frame.EP.yef_ctrl (Seq.create 1 0uy));
  rewrite (pts_to (Vec.vec_to_array soh) (Seq.create 133 0uy))
      as  (pts_to frame.EP.yef_soh (Seq.create 133 0uy));
  rewrite (pts_to (Vec.vec_to_array ack) (Seq.create 1 0uy))
      as  (pts_to frame.EP.yef_ack (Seq.create 1 0uy));
  rewrite (pts_to (Vec.vec_to_array ycnf) (Seq.create 128 0uy))
      as  (pts_to frame.EP.yef_ycnf (Seq.create 128 0uy));
  rewrite (pts_to outbuf o) as (pts_to frame.EP.yef_out o);
  rewrite (Vec.pts_to cursor (Seq.create 1 0sz))
      as  (Vec.pts_to frame.EP.yef_cursor (Seq.create 1 0sz));

  (* 3. Fold the endpoint's persistent resources, then re-present them as the
        instance's projected slprops so unification pins `drive_steps`. *)
  fold (EP.ymodem_client_payload_ready frame);
  fold (EP.ymodem_client_frame_ready i cfg frame YP.ymodem_client_initial);
  fold (EP.ymodem_client_io_ready i ch frame Seq.empty Seq.empty YP.ymodem_client_initial);

  rewrite (CC.ymodem_client_inv i Seq.empty Seq.empty YP.ymodem_client_initial)
      as  (CC.ymodem_client_protocol_implementation.CPI.pi_invariant
            i Seq.empty Seq.empty YP.ymodem_client_initial);
  rewrite (EP.ymodem_client_frame_ready i cfg frame YP.ymodem_client_initial)
      as  (EP.ymodem_client_protocol_endpoint.PE.pe_frame_ready
            i cfg frame YP.ymodem_client_initial);
  rewrite (EP.ymodem_client_io_ready i ch frame Seq.empty Seq.empty YP.ymodem_client_initial)
      as  (EP.ymodem_client_protocol_endpoint.PE.pe_io_ready
            i ch frame Seq.empty Seq.empty YP.ymodem_client_initial);

  (* 4. Run the GENERIC verified driver.  Implicits are given explicitly so the
        polymorphic protocol/endpoint dictionaries resolve unambiguously. *)
  let _res =
    PD.drive_steps
      #CC.ymodem_client_impl
      #YP.ymodem_client_state
      #YMsg.ymodem_message
      #YP.ymodem_client_local
      #unit
      #CC.ymodem_client_protocol_implementation
      #EP.ymodem_client_protocol_endpoint
      i cfg frame ch fuel
      (Ghost.hide #TCP.bytes Seq.empty)
      (Ghost.hide #TCP.bytes Seq.empty)
      (Ghost.hide YP.ymodem_client_initial);
  with received1 sent1 st1. _;

  (* 5. Tear down.  Re-present the instance slprops as the endpoint's own
        definitions, unfold to recover the buffers and free them; the channel
        and `outbuf` go back to the caller. *)
  rewrite (EP.ymodem_client_protocol_endpoint.PE.pe_frame_ready
            i cfg frame (Ghost.reveal st1))
      as  (EP.ymodem_client_frame_ready i cfg frame (Ghost.reveal st1));
  rewrite (EP.ymodem_client_protocol_endpoint.PE.pe_io_ready
            i ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1))
      as  (EP.ymodem_client_io_ready
            i ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1));
  rewrite (CC.ymodem_client_protocol_implementation.CPI.pi_invariant
            i (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1))
      as  (CC.ymodem_client_inv
            i (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1));

  unfold (EP.ymodem_client_frame_ready i cfg frame (Ghost.reveal st1));
  with d_final. _;
  unfold (EP.ymodem_client_payload_ready frame);
  with ob_final cv_final. _;
  unfold (EP.ymodem_client_io_ready
            i ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1));
  with raw_final ctrl_final soh_final ack_final. _;

  let nbytes = Vec.op_Dot_Lparen_Rparen frame.EP.yef_cursor 0sz;

  rewrite (pts_to frame.EP.yef_ycnf d_final) as (pts_to (Vec.vec_to_array ycnf) d_final);
  Vec.to_vec_pts_to ycnf;
  Vec.free ycnf;
  rewrite (pts_to frame.EP.yef_ctrl ctrl_final) as (pts_to (Vec.vec_to_array ctrl) ctrl_final);
  Vec.to_vec_pts_to ctrl;
  Vec.free ctrl;
  rewrite (pts_to frame.EP.yef_soh soh_final) as (pts_to (Vec.vec_to_array soh) soh_final);
  Vec.to_vec_pts_to soh;
  Vec.free soh;
  rewrite (pts_to frame.EP.yef_ack ack_final) as (pts_to (Vec.vec_to_array ack) ack_final);
  Vec.to_vec_pts_to ack;
  Vec.free ack;
  rewrite (Vec.pts_to frame.EP.yef_cursor cv_final) as (Vec.pts_to cursor cv_final);
  Vec.free cursor;
  rewrite (pts_to frame.EP.yef_out ob_final) as (pts_to outbuf ob_final);

  free_ymodem_client i #received1 #sent1 #st1;
  nbytes
}

(* ───────────────────────────────────────────────────────────────────────────
   Connect-style entry: connect, receive into `outbuf`, close.
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
fn run_ymodem_client_connect
  (host:array U8.t)
  (host_len:SZ.t)
  (port:U16.t)
  (outbuf:array U8.t)
  (outcap:SZ.t)
  (fuel:SZ.t)
  (#filename:Ghost.erased TCP.bytes)
  (#len:Ghost.erased nat)
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
      (* `connect_tcp` yields the empty history as `Seq.create 0 0uy`; the runner
         wants it as `Seq.empty`.  They are extensionally equal (both length 0). *)
      assert (pure (Seq.equal (Seq.create 0 0uy) (Seq.empty #U8.t)));
      rewrite (TCP.is_channel ch (Seq.create 0 0uy) (Seq.create 0 0uy))
          as  (TCP.is_channel ch Seq.empty Seq.empty);
      let _n = ymodem_client_receive ch outbuf outcap fuel #filename #len;
      TCP.close ch
    }
    None -> {
      ()
    }
  }
}
