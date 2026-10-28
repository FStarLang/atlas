module TFTP.Impl.Server.Socket

(**
  Verified runner that drives the TFTP *server* (sender) over a `Common.TCP`
  channel using the GENERIC verified loop `Common.ProtocolDriver.drive_steps`
  specialised to the committed instances
  `TFTP.Impl.Server.CanonicalProtocol.tftp_server_protocol_implementation`
  (the state-machine implementation dictionary) and
  `TFTP.Impl.Server.Endpoint.tftp_server_protocol_endpoint` (the scheduling +
  resource dictionary).

  `tftp_server_send` is the C entry point: it allocates the endpoint's cells
  and buffers, runs the driver (Server_start, then DATA #1..#nblocks each
  awaiting its ACK, then Server_complete), frees everything it allocated and
  returns the number of blocks sent and acknowledged.  The channel is left open
  (owned by the C glue) and the file is only read.  The file's contents and
  name are specification-only (erased arguments), so the endpoint config
  passed to `drive_steps` is built here and Custard specialises the driver to
  it.

  Custard extracts this module (the driver and both dictionaries are
  monomorphised); `run_tftp_server_connect` is a verified convenience wrapper
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
module L    = FStar.List.Tot

module TP   = TFTP.Protocol
module CC   = TFTP.Impl.Server.CanonicalProtocol
module EP   = TFTP.Impl.Server.Endpoint
module Log  = TFTP.Impl.Server.Log
module TW   = TFTP.Wire

#set-options "--fuel 1 --ifuel 1 --z3rlimit 10"

(* ───────────────────────────────────────────────────────────────────────────
   Impl-handle disposal: `Vec.free` the status and expected cells, `drop_` the
   (affine) ghost progress reference.
   ─────────────────────────────────────────────────────────────────────────── *)

fn free_tftp_server
  (i:CC.tftp_server_impl)
  (#received:erased TCP.bytes)
  (#sent:erased TCP.bytes)
  (#st:erased TP.tftp_server_state)
requires
  CC.tftp_server_inv i received sent st **
  pure (Vec.is_full_vec i.CC.status /\ Vec.is_full_vec i.CC.expected)
ensures emp
{
  unfold (CC.tftp_server_inv i received sent st);
  with svs evs. _;
  Vec.free i.CC.status;
  Vec.free i.CC.expected;
  drop_ (MR.pts_to i.CC.progress #1.0R (Log.mk_log received sent st))
}

(* ───────────────────────────────────────────────────────────────────────────
   The runner: drive the sender over an already-connected channel.

   The caller owns the file (`nbytes` bytes, cut into `nblocks = nbytes/512 + 1`
   unpadded blocks, the last one short).  The server only READS it, so the
   `Vec.pts_to` is returned intact.
   ─────────────────────────────────────────────────────────────────────────── *)

fn tftp_server_send
  (ch:TCP.channel)
  (file:Vec.vec U8.t)
  (nblocks:SZ.t)
  (nbytes:SZ.t)
  (fuel:SZ.t)
  (#contents:Ghost.erased (Seq.seq U8.t))
  (#filename:Ghost.erased TCP.bytes)
requires
  TCP.is_channel ch Seq.empty Seq.empty **
  Vec.pts_to file contents **
  pure (Seq.length contents == SZ.v nbytes /\
        SZ.v nblocks == SZ.v nbytes / 512 + 1 /\
        SZ.v nblocks <= 65534)
returns nsent:SZ.t
ensures
  (exists* (r s:TCP.bytes). TCP.is_channel ch r s) **
  Vec.pts_to file contents
{
  let cfg : EP.tftp_server_config = {
    EP.scfg_file       = file;
    EP.scfg_contents   = contents;
    EP.scfg_nbytes_sz  = nbytes;
    EP.scfg_nblocks    = Ghost.hide (SZ.v nblocks);
    EP.scfg_nblocks_sz = nblocks;
    EP.scfg_filename   = filename;
  };
  rewrite (Vec.pts_to file contents) as (Vec.pts_to cfg.EP.scfg_file cfg.EP.scfg_contents);

  (* 1. Fresh sender handle (pi_invariant at the initial state). *)
  let i = CC.new_tftp_server ();

  (* 2. Allocate the endpoint's persistent state.  The two cells stay as `Vec`
        handles; the four scratch buffers become raw-array points-to. *)
  let cursor  = Vec.alloc 0sz 1sz;    // blocks sent so far
  let started = Vec.alloc 0uy 1sz;    // 1uy iff Server_start fired
  let blk_v   = Vec.alloc 0uy 512sz;  // payload scratch (sef_blk)
  let tsnf_v  = Vec.alloc 0uy 516sz;  // process_network scratch (sef_tsnf)
  let out_v   = Vec.alloc 0uy 516sz;  // DATA output buffer (sef_out)
  let in_v    = Vec.alloc 0uy 4sz;    // ACK input (sef_in)
  Vec.to_array_pts_to blk_v;
  Vec.to_array_pts_to tsnf_v;
  Vec.to_array_pts_to out_v;
  Vec.to_array_pts_to in_v;

  let frame : EP.tftp_server_endpoint_frame = {
    EP.sef_cursor  = cursor;
    EP.sef_started = started;
    EP.sef_blk     = Vec.vec_to_array blk_v;
    EP.sef_tsnf    = Vec.vec_to_array tsnf_v;
    EP.sef_out     = Vec.vec_to_array out_v;
    EP.sef_in      = Vec.vec_to_array in_v;
  };
  rewrite (Vec.pts_to cursor (Seq.create 1 0sz))
      as  (Vec.pts_to frame.EP.sef_cursor (Seq.create 1 0sz));
  rewrite (Vec.pts_to started (Seq.create 1 0uy))
      as  (Vec.pts_to frame.EP.sef_started (Seq.create 1 0uy));
  rewrite (pts_to (Vec.vec_to_array blk_v) (Seq.create 512 0uy))
      as  (pts_to frame.EP.sef_blk (Seq.create 512 0uy));
  rewrite (pts_to (Vec.vec_to_array tsnf_v) (Seq.create 516 0uy))
      as  (pts_to frame.EP.sef_tsnf (Seq.create 516 0uy));
  rewrite (pts_to (Vec.vec_to_array out_v) (Seq.create 516 0uy))
      as  (pts_to frame.EP.sef_out (Seq.create 516 0uy));
  rewrite (pts_to (Vec.vec_to_array in_v) (Seq.create 4 0uy))
      as  (pts_to frame.EP.sef_in (Seq.create 4 0uy));

  (* 3. Discharge the coupling at the initial state, fold the endpoint's
        persistent resources, then re-present them as the instance's projected
        slprops so unification pins `drive_steps`. *)
  assert (pure (TP.tftp_server_initial.TP.tss_filename == None));
  assert (pure (L.length TP.tftp_server_initial.TP.tss_sent == 0));

  fold (EP.tftp_server_frame_ready i cfg frame TP.tftp_server_initial);
  fold (EP.tftp_server_io_ready i ch frame Seq.empty Seq.empty TP.tftp_server_initial);

  rewrite (CC.tftp_server_inv i Seq.empty Seq.empty TP.tftp_server_initial)
      as  (CC.tftp_server_protocol_implementation.CPI.pi_invariant
            i Seq.empty Seq.empty TP.tftp_server_initial);
  rewrite (EP.tftp_server_frame_ready i cfg frame TP.tftp_server_initial)
      as  (EP.tftp_server_protocol_endpoint.PE.pe_frame_ready
            i cfg frame TP.tftp_server_initial);
  rewrite (EP.tftp_server_io_ready i ch frame Seq.empty Seq.empty TP.tftp_server_initial)
      as  (EP.tftp_server_protocol_endpoint.PE.pe_io_ready
            i ch frame Seq.empty Seq.empty TP.tftp_server_initial);

  (* 4. Run the GENERIC verified driver. *)
  let _res =
    PD.drive_steps
      #CC.tftp_server_impl
      #TP.tftp_server_state
      #TW.tftp_message
      #TP.tftp_server_local
      #unit
      #CC.tftp_server_protocol_implementation
      #EP.tftp_server_protocol_endpoint
      i cfg frame ch fuel
      (Ghost.hide #TCP.bytes Seq.empty)
      (Ghost.hide #TCP.bytes Seq.empty)
      (Ghost.hide TP.tftp_server_initial);
  with received1 sent1 st1. _;

  (* 5. Tear down: unfold, read the cursor, free what we allocated; the channel
        and the file go back to the caller. *)
  rewrite (EP.tftp_server_protocol_endpoint.PE.pe_frame_ready
            i cfg frame (Ghost.reveal st1))
      as  (EP.tftp_server_frame_ready i cfg frame (Ghost.reveal st1));
  rewrite (EP.tftp_server_protocol_endpoint.PE.pe_io_ready
            i ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1))
      as  (EP.tftp_server_io_ready
            i ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1));
  rewrite (CC.tftp_server_protocol_implementation.CPI.pi_invariant
            i (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1))
      as  (CC.tftp_server_inv
            i (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1));

  unfold (EP.tftp_server_frame_ready i cfg frame (Ghost.reveal st1));
  with cv_f bv_f blk_f tsnf_f. _;
  unfold (EP.tftp_server_io_ready
            i ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1));
  with raw_f out_f in_f. _;

  let nsent = Vec.op_Dot_Lparen_Rparen frame.EP.sef_cursor 0sz;

  rewrite (pts_to frame.EP.sef_blk blk_f) as (pts_to (Vec.vec_to_array blk_v) blk_f);
  Vec.to_vec_pts_to blk_v;
  Vec.free blk_v;
  rewrite (pts_to frame.EP.sef_tsnf tsnf_f) as (pts_to (Vec.vec_to_array tsnf_v) tsnf_f);
  Vec.to_vec_pts_to tsnf_v;
  Vec.free tsnf_v;
  rewrite (pts_to frame.EP.sef_out out_f) as (pts_to (Vec.vec_to_array out_v) out_f);
  Vec.to_vec_pts_to out_v;
  Vec.free out_v;
  rewrite (pts_to frame.EP.sef_in in_f) as (pts_to (Vec.vec_to_array in_v) in_f);
  Vec.to_vec_pts_to in_v;
  Vec.free in_v;
  rewrite (Vec.pts_to frame.EP.sef_cursor cv_f) as (Vec.pts_to cursor cv_f);
  Vec.free cursor;
  rewrite (Vec.pts_to frame.EP.sef_started bv_f) as (Vec.pts_to started bv_f);
  Vec.free started;

  free_tftp_server i #received1 #sent1 #st1;
  rewrite (Vec.pts_to cfg.EP.scfg_file cfg.EP.scfg_contents) as (Vec.pts_to file contents);
  nsent
}

(* ───────────────────────────────────────────────────────────────────────────
   Connect-style entry: connect, send, close; the host buffer and the file are
   both returned intact.
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
fn run_tftp_server_connect
  (host:array U8.t)
  (host_len:SZ.t)
  (port:U16.t)
  (file:Vec.vec U8.t)
  (nblocks:SZ.t)
  (nbytes:SZ.t)
  (fuel:SZ.t)
  (#contents:Ghost.erased (Seq.seq U8.t))
  (#filename:Ghost.erased TCP.bytes)
requires
  pts_to host 'h **
  Vec.pts_to file contents **
  pure (Seq.length 'h == SZ.v host_len /\
        Seq.length contents == SZ.v nbytes /\
        SZ.v nblocks == SZ.v nbytes / 512 + 1 /\
        SZ.v nblocks <= 65534)
ensures
  pts_to host 'h **
  Vec.pts_to file contents
{
  match TCP.connect_tcp host host_len port {
    Some ch -> {
      assert (pure (Seq.equal (Seq.create 0 0uy) (Seq.empty #U8.t)));
      rewrite (TCP.is_channel ch (Seq.create 0 0uy) (Seq.create 0 0uy))
          as  (TCP.is_channel ch Seq.empty Seq.empty);
      let _n = tftp_server_send ch file nblocks nbytes fuel #contents #filename;
      TCP.close ch
    }
    None -> {
      ()
    }
  }
}
