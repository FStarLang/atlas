module TFTP.Impl.Client.Endpoint

(**
  TFTP *client* (receiver) driver-facing endpoint: a full 28-field instance of
  `Common.ProtocolEndpoint.protocol_endpoint` over the committed dictionary
  `TFTP.Impl.Client.CanonicalProtocol.tftp_client_protocol_implementation`.

  This is the executable scheduling + resource layer that lets the GENERIC
  verified loop `Common.ProtocolDriver.drive_steps` run the receiver (no loop is
  written here).  Structural mirror of `YModem.Impl.Client.Endpoint`:

    1. `pe_next_action` reads the runtime status cell and SCHEDULES:
         status 0uy (fresh, filename None) -> EndpointLocal (Client_start ...)  (bootstrap)
         status 1uy (receiving)            -> EndpointNeedInput                 (await a datagram)
         status 2uy (completed)            -> EndpointDone
         status 3uy (aborted)              -> EndpointFailed

    2. `pe_prepare_network` reads ONE datagram (at most 516 bytes) into the
       datagram buffer and hands the handler a concrete sub-array view of
       exactly the `n` received bytes (the network frame precondition keeps
       `input_len == Seq.length input_contents`).  The rest of the datagram
       buffer is kept, masked, in the network-I/O continuation, and
       `pe_finish_network_io` joins the view back.

    3. Payload delivery: `pe_finish_network_io` (which still owns the datagram
       bytes) appends `datagram[4..n)` to the caller's reconstruction buffer
       (`tef_out`, `tef_outcap` bytes) at the cursor whenever the handler
       answered with an ACK (`process_produced_len == 4`, i.e. an accepted
       DATA block).  This is bounds-checked; the content is not specified.

  Config note: the receiver's filename is specification-only (`Ghost.erased`,
  as is the `Client_start` field), so the extracted config carries no data.

  Extracted to C by Custard (which monomorphises the dictionary away) as part
  of the runner `tftp_client_receive` in `TFTP.Impl.Client.Socket`.
**)

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module CPI = Common.ProtocolImplementation
module PE = Common.ProtocolEndpoint
module SZ = FStar.SizeT
module Seq = FStar.Seq
module TCP = Common.TCP
module U8 = FStar.UInt8
module Vec = Pulse.Lib.Vec
module AC = Pulse.Lib.Array.Core
module A = Pulse.Lib.Array

module TP = TFTP.Protocol
module CC = TFTP.Impl.Client.CanonicalProtocol

open TFTP.Wire

#set-options "--fuel 1 --ifuel 1 --z3rlimit 10"

(* ───────────────────────────────────────────────────────────────────────────
   Endpoint config (§ pe_config)
   ─────────────────────────────────────────────────────────────────────────── *)

(* Specification-only filename that seeds the receiver's `Client_start`. *)
noeq
type tftp_client_config = {
  tcfg_filename : Ghost.erased TCP.bytes;
}

(* ───────────────────────────────────────────────────────────────────────────
   Endpoint frame (§ pe_frame): the persistent concrete I/O buffers
   ─────────────────────────────────────────────────────────────────────────── *)

noeq
type tftp_client_endpoint_frame = {
  tef_dgram   : array U8.t;   // 516-byte datagram buffer (max DATA datagram)
  tef_ack     : array U8.t;   // 4-byte output buffer: the ACK the receiver emits
  tef_scratch : array U8.t;   // 512-byte scratch handed to process_network (tcnf_buf)
  tef_out     : array U8.t;   // caller's reconstruction buffer (tef_outcap bytes)
  tef_outcap  : SZ.t;
  tef_cursor  : Vec.vec SZ.t; // 1-cell: bytes written to tef_out so far
}

(* ───────────────────────────────────────────────────────────────────────────
   Persistent slprops (§ pe_frame_ready, pe_io_ready)
   ─────────────────────────────────────────────────────────────────────────── *)

(* The payload sink: the reconstruction buffer and its cursor. *)
let tftp_client_payload_ready (frame:tftp_client_endpoint_frame) : slprop =
  exists* (ob:Seq.seq U8.t) (cv:Seq.seq SZ.t).
    pts_to frame.tef_out ob **
    Vec.pts_to frame.tef_cursor cv **
    pure (
      Seq.length ob == SZ.v frame.tef_outcap /\
      Seq.length cv == 1 /\
      SZ.v (Seq.index cv 0) <= SZ.v frame.tef_outcap)

(* frame_ready owns the 512-byte scratch: the network frame post-condition owns
   `tcnf_buf`, so finishing a network action re-establishes frame_ready. *)
let tftp_client_frame_ready
  (_i:CC.tftp_client_impl)
  (_cfg:tftp_client_config)
  (frame:tftp_client_endpoint_frame)
  (_st:TP.tftp_client_state)
  : slprop =
  exists* (d:Seq.seq U8.t).
    pts_to frame.tef_scratch d **
    pure (Seq.length d == 512)

(* io_ready owns the channel, the datagram + ACK buffers and the payload sink.
   The raw received history is existential (decoupled from the abstract
   `received`). *)
let tftp_client_io_ready
  (_i:CC.tftp_client_impl)
  (ch:TCP.channel)
  (frame:tftp_client_endpoint_frame)
  (_received:TCP.bytes)
  (sent:TCP.bytes)
  (_st:TP.tftp_client_state)
  : slprop =
  (exists* (raw:TCP.bytes) (dg:Seq.seq U8.t) (ack_b:Seq.seq U8.t).
    TCP.is_channel ch raw sent **
    pts_to frame.tef_dgram dg **
    pts_to frame.tef_ack ack_b **
    pure (Seq.length dg == 516 /\ Seq.length ack_b == 4)) **
  tftp_client_payload_ready frame

(* ───────────────────────────────────────────────────────────────────────────
   Action frame (§ pe_action_frame) and action continuations
   ─────────────────────────────────────────────────────────────────────────── *)

let tftp_client_action_frame
  (i:CC.tftp_client_impl)
  (cfg:tftp_client_config)
  (frame:tftp_client_endpoint_frame)
  (st:TP.tftp_client_state)
  (action:PE.endpoint_action
    CC.tftp_client_network_frame
    TP.tftp_client_local
    CC.tftp_client_local_frame)
  : slprop =
  match action with
  | PE.EndpointNeedInput network_frame ->
    tftp_client_frame_ready i cfg frame st **
    pure (network_frame.CC.tcnf_buf == frame.tef_scratch)
  | PE.EndpointLocal _ _ ->
    tftp_client_frame_ready i cfg frame st
  | PE.EndpointDone
  | PE.EndpointFailed ->
    tftp_client_frame_ready i cfg frame st

let tftp_client_network_continuation
  (_i:CC.tftp_client_impl)
  (_cfg:tftp_client_config)
  (frame:tftp_client_endpoint_frame)
  (_st:TP.tftp_client_state)
  (network_frame:CC.tftp_client_network_frame)
  : slprop =
  pure (network_frame.CC.tcnf_buf == frame.tef_scratch)

let tftp_client_local_continuation
  (_i:CC.tftp_client_impl)
  (_cfg:tftp_client_config)
  (frame:tftp_client_endpoint_frame)
  (_st:TP.tftp_client_state)
  (_ev:TP.tftp_client_local)
  (_local_frame:CC.tftp_client_local_frame)
  : slprop =
  exists* (d:Seq.seq U8.t).
    pts_to frame.tef_scratch d **
    pure (Seq.length d == 512)

(* ───────────────────────────────────────────────────────────────────────────
   Datagram prefix views: lend `dgram[0..n)` as an exact-length array, keeping
   the (masked) remainder of the 516-byte buffer aside.
   ─────────────────────────────────────────────────────────────────────────── *)

let prefix_view (parent v:array U8.t) (n:nat) : prop =
  if n <= AC.length parent then v == AC.gsub parent 0 n else False

let dgram_rest (buf:array U8.t) (n:SZ.t) : slprop =
  exists* (s:Seq.seq (option U8.t)).
    AC.pts_to_mask buf s (fun k -> ~(k < SZ.v n)) **
    pure (
      Seq.length s == 516 /\
      (forall (k:nat). k < Seq.length s ==> Some? (Seq.index s k)))

fn take_prefix (buf:array U8.t) (n:SZ.t) (#c:Ghost.erased (Seq.seq U8.t))
requires
  pts_to buf c **
  pure (Seq.length c == 516 /\ SZ.v n <= 516)
returns v:array U8.t
ensures exists* (pc:Seq.seq U8.t).
  pts_to v pc **
  dgram_rest buf n **
  pure (Seq.length pc == SZ.v n /\ prefix_view buf v (SZ.v n))
{
  pts_to_len buf;
  to_mask buf;
  let v = AC.sub buf 0sz (SZ.v n);
  AC.mask_mext buf (fun k -> ~(k < SZ.v n));
  fold (dgram_rest buf n);
  from_mask v;
  pts_to_len v;
  v
}

ghost
fn give_back_prefix
  (buf:array U8.t) (n:SZ.t) (v:array U8.t)
  (#pc:Ghost.erased (Seq.seq U8.t))
requires
  pts_to v pc **
  dgram_rest buf n **
  pure (Seq.length pc == SZ.v n /\ prefix_view buf v (SZ.v n))
ensures exists* (c:Seq.seq U8.t).
  pts_to buf c **
  pure (Seq.length c == 516)
{
  unfold (dgram_rest buf n);
  with s. _;
  to_mask v;
  with sv. _;
  rewrite (AC.pts_to_mask v sv (fun _ -> True))
    as (AC.pts_to_mask (AC.gsub buf 0 (SZ.v n)) sv (fun _ -> True));
  AC.return_sub buf #1.0R #s #sv #(fun k -> ~(k < SZ.v n)) #(fun _ -> True) #0 #(SZ.v n);
  from_mask buf;
}

(* ───────────────────────────────────────────────────────────────────────────
   Network I/O carrier (§ pe_network_io) + continuation + accessors
   ─────────────────────────────────────────────────────────────────────────── *)

noeq
type tftp_client_endpoint_network_io = {
  tni_input          : array U8.t;   // view of tef_dgram[0..tni_input_len)
  tni_input_len      : SZ.t;
  tni_output         : array U8.t;   // tef_ack
  tni_input_contents : Ghost.erased TCP.bytes;
  tni_old_output     : Ghost.erased TCP.bytes;
  tni_raw_received   : Ghost.erased TCP.bytes;
}

let tftp_client_network_io_continuation
  (_i:CC.tftp_client_impl)
  (ch:TCP.channel)
  (frame:tftp_client_endpoint_frame)
  (_received:TCP.bytes)
  (sent:TCP.bytes)
  (_st:TP.tftp_client_state)
  (nio:tftp_client_endpoint_network_io)
  : slprop =
  TCP.is_channel ch (Ghost.reveal nio.tni_raw_received) sent **
  dgram_rest frame.tef_dgram nio.tni_input_len **
  tftp_client_payload_ready frame **
  pure (
    nio.tni_output == frame.tef_ack /\
    Seq.length (Ghost.reveal nio.tni_old_output) == 4 /\
    Seq.length (Ghost.reveal nio.tni_input_contents) == SZ.v nio.tni_input_len /\
    prefix_view frame.tef_dgram nio.tni_input (SZ.v nio.tni_input_len))

let tftp_client_network_input (nio:tftp_client_endpoint_network_io) : array U8.t =
  nio.tni_input

let tftp_client_network_input_len (nio:tftp_client_endpoint_network_io) : SZ.t =
  nio.tni_input_len

let tftp_client_network_output (nio:tftp_client_endpoint_network_io) : array U8.t =
  nio.tni_output

let tftp_client_network_output_len (_nio:tftp_client_endpoint_network_io) : SZ.t =
  4sz

let tftp_client_network_input_contents (nio:tftp_client_endpoint_network_io)
  : Ghost.erased TCP.bytes =
  nio.tni_input_contents

let tftp_client_network_old_output (nio:tftp_client_endpoint_network_io)
  : Ghost.erased TCP.bytes =
  nio.tni_old_output

(* ───────────────────────────────────────────────────────────────────────────
   pe_next_action — read the status cell and schedule
   ─────────────────────────────────────────────────────────────────────────── *)

fn tftp_client_next_action
  (i:CC.tftp_client_impl)
  (cfg:tftp_client_config)
  (frame:tftp_client_endpoint_frame)
  (received:Ghost.erased TCP.bytes)
  (sent:Ghost.erased TCP.bytes)
  (st:Ghost.erased TP.tftp_client_state)
requires
  CC.tftp_client_inv i (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) **
  tftp_client_frame_ready i cfg frame (Ghost.reveal st)
returns action:PE.endpoint_action
  CC.tftp_client_network_frame
  TP.tftp_client_local
  CC.tftp_client_local_frame
ensures
  CC.tftp_client_inv i (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) **
  tftp_client_action_frame i cfg frame (Ghost.reveal st) action **
  pure (PE.action_not_internal CC.tftp_client_protocol_implementation action)
{
  unfold (CC.tftp_client_inv i (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  with svs. _;
  let s = Vec.op_Dot_Lparen_Rparen i.CC.status 0sz;
  fold (CC.tftp_client_inv i (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  if (s = 0uy) {
    fold (tftp_client_action_frame i cfg frame (Ghost.reveal st)
      (PE.EndpointLocal (TP.Client_start cfg.tcfg_filename) ()));
    PE.EndpointLocal (TP.Client_start cfg.tcfg_filename) ()
  } else if (s = 1uy) {
    let nf : CC.tftp_client_network_frame = { CC.tcnf_buf = frame.tef_scratch };
    fold (tftp_client_action_frame i cfg frame (Ghost.reveal st) (PE.EndpointNeedInput nf));
    PE.EndpointNeedInput nf
  } else if (s = 2uy) {
    fold (tftp_client_action_frame i cfg frame (Ghost.reveal st) PE.EndpointDone);
    PE.EndpointDone
  } else {
    fold (tftp_client_action_frame i cfg frame (Ghost.reveal st) PE.EndpointFailed);
    PE.EndpointFailed
  }
}

(* ───────────────────────────────────────────────────────────────────────────
   pe_cancel_action
   ─────────────────────────────────────────────────────────────────────────── *)

fn tftp_client_cancel_action
  (i:CC.tftp_client_impl)
  (cfg:tftp_client_config)
  (frame:tftp_client_endpoint_frame)
  (st:Ghost.erased TP.tftp_client_state)
  (action:PE.endpoint_action
    CC.tftp_client_network_frame
    TP.tftp_client_local
    CC.tftp_client_local_frame)
requires tftp_client_action_frame i cfg frame (Ghost.reveal st) action
ensures tftp_client_frame_ready i cfg frame (Ghost.reveal st)
{
  match action {
    PE.EndpointNeedInput network_frame -> {
      unfold (tftp_client_action_frame i cfg frame (Ghost.reveal st) (PE.EndpointNeedInput network_frame))
    }
    PE.EndpointLocal ev local_frame -> {
      unfold (tftp_client_action_frame i cfg frame (Ghost.reveal st) (PE.EndpointLocal ev local_frame))
    }
    PE.EndpointDone -> {
      unfold (tftp_client_action_frame i cfg frame (Ghost.reveal st) PE.EndpointDone)
    }
    PE.EndpointFailed -> {
      unfold (tftp_client_action_frame i cfg frame (Ghost.reveal st) PE.EndpointFailed)
    }
  }
}

(* ───────────────────────────────────────────────────────────────────────────
   pe_prepare_network — read one datagram, lend its exact-length prefix
   ─────────────────────────────────────────────────────────────────────────── *)

fn tftp_client_prepare_network
  (i:CC.tftp_client_impl)
  (cfg:tftp_client_config)
  (frame:tftp_client_endpoint_frame)
  (ch:TCP.channel)
  (network_frame:CC.tftp_client_network_frame)
  (received:Ghost.erased TCP.bytes)
  (sent:Ghost.erased TCP.bytes)
  (st:Ghost.erased TP.tftp_client_state)
requires
  tftp_client_action_frame i cfg frame (Ghost.reveal st) (PE.EndpointNeedInput network_frame) **
  tftp_client_io_ready i ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st)
returns nio:tftp_client_endpoint_network_io
ensures
  tftp_client_network_io_continuation i ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) nio **
  PE.network_buffers
    (tftp_client_network_input nio)
    (tftp_client_network_input_len nio)
    (tftp_client_network_output nio)
    (tftp_client_network_output_len nio)
    (Ghost.reveal (tftp_client_network_input_contents nio))
    (Ghost.reveal (tftp_client_network_old_output nio)) **
  CC.tftp_client_network_frame_pre
    network_frame
    (tftp_client_network_input nio)
    (tftp_client_network_input_len nio)
    (tftp_client_network_output nio)
    (tftp_client_network_output_len nio)
    (Ghost.reveal (tftp_client_network_input_contents nio))
    (Ghost.reveal (tftp_client_network_old_output nio)) **
  tftp_client_network_continuation i cfg frame (Ghost.reveal st) network_frame **
  pure (
    CPI.buffers_wf
      (Ghost.reveal (tftp_client_network_input_contents nio))
      (tftp_client_network_input_len nio)
      (Ghost.reveal (tftp_client_network_old_output nio))
      (tftp_client_network_output_len nio))
{
  unfold (tftp_client_action_frame i cfg frame (Ghost.reveal st) (PE.EndpointNeedInput network_frame));
  unfold (tftp_client_frame_ready i cfg frame (Ghost.reveal st));
  with scratch_d. _;
  unfold (tftp_client_io_ready i ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  with raw dg ack_b. _;
  (* one datagram (at most 516 bytes) *)
  let n = TCP.read ch frame.tef_dgram 516sz;
  with dg1 chunk. _;
  let v = take_prefix frame.tef_dgram n;
  with pc. _;
  let nio : tftp_client_endpoint_network_io = {
    tni_input = v;
    tni_input_len = n;
    tni_output = frame.tef_ack;
    tni_input_contents = Ghost.hide pc;
    tni_old_output = Ghost.hide ack_b;
    tni_raw_received = Ghost.hide (Seq.append raw chunk);
  };
  rewrite (TCP.is_channel ch (Seq.append raw chunk) (Ghost.reveal sent))
    as (TCP.is_channel ch (Ghost.reveal nio.tni_raw_received) (Ghost.reveal sent));
  rewrite (dgram_rest frame.tef_dgram n)
    as (dgram_rest frame.tef_dgram nio.tni_input_len);
  fold (tftp_client_network_io_continuation i ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) nio);
  rewrite (pts_to v pc)
    as (pts_to (tftp_client_network_input nio) (Ghost.reveal (tftp_client_network_input_contents nio)));
  rewrite (pts_to frame.tef_ack ack_b)
    as (pts_to (tftp_client_network_output nio) (Ghost.reveal (tftp_client_network_old_output nio)));
  fold (PE.network_buffers
    (tftp_client_network_input nio)
    (tftp_client_network_input_len nio)
    (tftp_client_network_output nio)
    (tftp_client_network_output_len nio)
    (Ghost.reveal (tftp_client_network_input_contents nio))
    (Ghost.reveal (tftp_client_network_old_output nio)));
  assert (pure (network_frame.CC.tcnf_buf == frame.tef_scratch));
  rewrite (pts_to frame.tef_scratch scratch_d)
    as (pts_to network_frame.CC.tcnf_buf scratch_d);
  fold (CC.tftp_client_network_frame_pre
    network_frame
    (tftp_client_network_input nio)
    (tftp_client_network_input_len nio)
    (tftp_client_network_output nio)
    (tftp_client_network_output_len nio)
    (Ghost.reveal (tftp_client_network_input_contents nio))
    (Ghost.reveal (tftp_client_network_old_output nio)));
  fold (tftp_client_network_continuation i cfg frame (Ghost.reveal st) network_frame);
  nio
}

(* ───────────────────────────────────────────────────────────────────────────
   Payload delivery: copy `src[src_off..src_off+n)` into
   `dst[dst_off..dst_off+n)` through concrete sub-array views, and append one
   DATA payload to the payload sink.
   ─────────────────────────────────────────────────────────────────────────── *)

fn array_blit
  (dst:array U8.t) (dst_off:SZ.t) (src:array U8.t) (src_off:SZ.t) (n:SZ.t)
  (#dc #sc:Ghost.erased (Seq.seq U8.t))
requires
  pts_to dst dc ** pts_to src sc **
  pure (SZ.v dst_off + SZ.v n <= Seq.length dc /\ SZ.v src_off + SZ.v n <= Seq.length sc)
returns _:unit
ensures exists* (dc' sc':Seq.seq U8.t).
  pts_to dst dc' ** pts_to src sc' **
  pure (Seq.length dc' == Seq.length dc /\ Seq.length sc' == Seq.length sc)
{
  pts_to_len dst;
  pts_to_len src;
  to_mask src;
  let ssub = AC.sub src src_off (SZ.v src_off + SZ.v n);
  from_mask ssub;
  pts_to_len ssub;
  to_mask dst;
  let dsub = AC.sub dst dst_off (SZ.v dst_off + SZ.v n);
  from_mask dsub;
  pts_to_len dsub;
  let _sq = A.memcpy_l n ssub dsub;
  to_mask dsub;
  AC.return_sub dst;
  from_mask dst;
  to_mask ssub;
  AC.return_sub src;
  from_mask src;
  ()
}

(* If `is_data`, append the payload `dg[4..n)` of the accepted DATA datagram at
   the cursor (skipped if it would not fit). *)
fn tftp_client_deliver_payload
  (frame:tftp_client_endpoint_frame)
  (dg:array U8.t)
  (n:SZ.t)
  (is_data:bool)
  (#d:Ghost.erased (Seq.seq U8.t))
requires
  pts_to dg d **
  tftp_client_payload_ready frame **
  pure (Seq.length d == SZ.v n)
ensures exists* (d':Seq.seq U8.t).
  pts_to dg d' **
  tftp_client_payload_ready frame **
  pure (Seq.length d' == SZ.v n)
{
  unfold (tftp_client_payload_ready frame);
  with ob cv. _;
  if (is_data && SZ.gte n 4sz) {
    let payload_len = SZ.sub n 4sz;
    let c = Vec.op_Dot_Lparen_Rparen frame.tef_cursor 0sz;
    if (SZ.gte (SZ.sub frame.tef_outcap c) payload_len) {
      array_blit frame.tef_out c dg 4sz payload_len;
      Vec.op_Dot_Lparen_Rparen_Less_Minus frame.tef_cursor 0sz (SZ.add c payload_len);
      fold (tftp_client_payload_ready frame)
    } else {
      fold (tftp_client_payload_ready frame)
    }
  } else {
    fold (tftp_client_payload_ready frame)
  }
}

(* ───────────────────────────────────────────────────────────────────────────
   pe_finish_network_action
   ─────────────────────────────────────────────────────────────────────────── *)

fn tftp_client_finish_network_action
  (i:CC.tftp_client_impl)
  (cfg:tftp_client_config)
  (frame:tftp_client_endpoint_frame)
  (network_frame:CC.tftp_client_network_frame)
  (result:CPI.process_result)
  (input_contents:Ghost.erased TCP.bytes)
  (input_len:SZ.t)
  (old_out:Ghost.erased TCP.bytes)
  (out_contents:Ghost.erased TCP.bytes)
  (st0:Ghost.erased TP.tftp_client_state)
  (st1:Ghost.erased TP.tftp_client_state)
  (consumed:Ghost.erased TCP.bytes)
  (wire_outputs:Ghost.erased (list tftp_message))
  (local_outputs:Ghost.erased (list unit))
requires
  tftp_client_network_continuation i cfg frame (Ghost.reveal st0) network_frame **
  CC.tftp_client_network_frame_post
    network_frame
    result
    (Ghost.reveal input_contents)
    input_len
    (Ghost.reveal old_out)
    (Ghost.reveal out_contents)
    (Ghost.reveal st0)
    (Ghost.reveal st1)
    (Ghost.reveal consumed)
    (Ghost.reveal wire_outputs)
    (Ghost.reveal local_outputs)
ensures tftp_client_frame_ready i cfg frame (Ghost.reveal st1)
{
  unfold (tftp_client_network_continuation i cfg frame (Ghost.reveal st0) network_frame);
  unfold (CC.tftp_client_network_frame_post
    network_frame
    result
    (Ghost.reveal input_contents)
    input_len
    (Ghost.reveal old_out)
    (Ghost.reveal out_contents)
    (Ghost.reveal st0)
    (Ghost.reveal st1)
    (Ghost.reveal consumed)
    (Ghost.reveal wire_outputs)
    (Ghost.reveal local_outputs));
  with o'. _;
  rewrite (pts_to network_frame.CC.tcnf_buf o')
    as (pts_to frame.tef_scratch o');
  fold (tftp_client_frame_ready i cfg frame (Ghost.reveal st1))
}

(* ───────────────────────────────────────────────────────────────────────────
   pe_finish_network_io — write the ACK, deliver the payload, return the view
   ─────────────────────────────────────────────────────────────────────────── *)

fn tftp_client_finish_network_io
  (i:CC.tftp_client_impl)
  (ch:TCP.channel)
  (frame:tftp_client_endpoint_frame)
  (nio:tftp_client_endpoint_network_io)
  (result:CPI.process_result)
  (received0:Ghost.erased TCP.bytes)
  (sent0:Ghost.erased TCP.bytes)
  (st0:Ghost.erased TP.tftp_client_state)
  (received1:Ghost.erased TCP.bytes)
  (sent1:Ghost.erased TCP.bytes)
  (st1:Ghost.erased TP.tftp_client_state)
  (out_contents:Ghost.erased TCP.bytes)
  (consumed:Ghost.erased TCP.bytes)
  (wire_outputs:Ghost.erased (list tftp_message))
  (local_outputs:Ghost.erased (list unit))
requires
  tftp_client_network_io_continuation i ch frame (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) nio **
  pts_to (tftp_client_network_input nio) (Ghost.reveal (tftp_client_network_input_contents nio)) **
  pts_to (tftp_client_network_output nio) (Ghost.reveal out_contents) **
  pure (
    CPI.network_process_correct
      (CC.tftp_client_protocol_implementation.CPI.pi_system i)
      (Ghost.reveal (tftp_client_network_input_contents nio))
      (tftp_client_network_input_len nio)
      (Ghost.reveal (tftp_client_network_old_output nio))
      (Ghost.reveal out_contents)
      (tftp_client_network_output_len nio)
      (Ghost.reveal received0)
      (Ghost.reveal sent0)
      (Ghost.reveal st0)
      result
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1)
      (Ghost.reveal consumed)
      (Ghost.reveal wire_outputs)
      (Ghost.reveal local_outputs))
ensures tftp_client_io_ready i ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1)
{
  unfold (tftp_client_network_io_continuation i ch frame (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) nio);
  CPI.lemma_network_process_sent_output_prefix
    (CC.tftp_client_protocol_implementation.CPI.pi_system i)
    (Ghost.reveal (tftp_client_network_input_contents nio))
    (tftp_client_network_input_len nio)
    (Ghost.reveal (tftp_client_network_old_output nio))
    (Ghost.reveal out_contents)
    (tftp_client_network_output_len nio)
    (Ghost.reveal received0)
    (Ghost.reveal sent0)
    (Ghost.reveal st0)
    result
    (Ghost.reveal received1)
    (Ghost.reveal sent1)
    (Ghost.reveal st1)
    (Ghost.reveal consumed)
    (Ghost.reveal wire_outputs)
    (Ghost.reveal local_outputs);
  assert (pure (SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)));
  let nwritten = TCP.write ch (tftp_client_network_output nio) result.CPI.process_produced_len;
  assert (pure (nwritten == result.CPI.process_produced_len));
  rewrite
    (TCP.is_channel
      ch
      (Ghost.reveal nio.tni_raw_received)
      (Seq.append
        (Ghost.reveal sent0)
        (if SZ.v nwritten <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v nwritten)
         else Seq.create 0 0uy)))
    as
    (TCP.is_channel
      ch
      (Ghost.reveal nio.tni_raw_received)
      (Seq.append
        (Ghost.reveal sent0)
        (if SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v result.CPI.process_produced_len)
         else Seq.create 0 0uy)));
  assert (pure (Seq.equal
    (Ghost.reveal sent1)
    (Seq.append
      (Ghost.reveal sent0)
      (CPI.output_prefix (Ghost.reveal out_contents) result.CPI.process_produced_len))));
  rewrite
    (TCP.is_channel
      ch
      (Ghost.reveal nio.tni_raw_received)
      (Seq.append
        (Ghost.reveal sent0)
        (if SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v result.CPI.process_produced_len)
         else Seq.create 0 0uy)))
    as
    (TCP.is_channel ch (Ghost.reveal nio.tni_raw_received) (Ghost.reveal sent1));
  (* An accepted DATA datagram was answered with a 4-byte ACK: append its
     payload `input[4..n)` to the caller's buffer. *)
  rewrite (pts_to (tftp_client_network_input nio) (Ghost.reveal (tftp_client_network_input_contents nio)))
    as (pts_to nio.tni_input (Ghost.reveal nio.tni_input_contents));
  tftp_client_deliver_payload frame nio.tni_input nio.tni_input_len
    (result.CPI.process_produced_len = 4sz);
  give_back_prefix frame.tef_dgram nio.tni_input_len nio.tni_input;
  rewrite (pts_to (tftp_client_network_output nio) (Ghost.reveal out_contents))
    as (pts_to frame.tef_ack (Ghost.reveal out_contents));
  fold (tftp_client_io_ready i ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1))
}

(* ───────────────────────────────────────────────────────────────────────────
   Local I/O carrier (§ pe_local_io) + continuation + accessors
   ─────────────────────────────────────────────────────────────────────────── *)

noeq
type tftp_client_endpoint_local_io = {
  tlo_output       : array U8.t;
  tlo_old_output   : Ghost.erased TCP.bytes;
  tlo_raw_received : Ghost.erased TCP.bytes;
  tlo_dgram_contents : Ghost.erased TCP.bytes;
}

let tftp_client_local_io_continuation
  (_i:CC.tftp_client_impl)
  (ch:TCP.channel)
  (frame:tftp_client_endpoint_frame)
  (_received:TCP.bytes)
  (sent:TCP.bytes)
  (_st:TP.tftp_client_state)
  (_ev:TP.tftp_client_local)
  (lio:tftp_client_endpoint_local_io)
  : slprop =
  TCP.is_channel ch (Ghost.reveal lio.tlo_raw_received) sent **
  pts_to frame.tef_dgram (Ghost.reveal lio.tlo_dgram_contents) **
  tftp_client_payload_ready frame **
  pure (
    lio.tlo_output == frame.tef_ack /\
    Seq.length (Ghost.reveal lio.tlo_old_output) == 4 /\
    Seq.length (Ghost.reveal lio.tlo_dgram_contents) == 516)

let tftp_client_local_output (lio:tftp_client_endpoint_local_io) : array U8.t =
  lio.tlo_output

let tftp_client_local_output_len (_lio:tftp_client_endpoint_local_io) : SZ.t =
  4sz

let tftp_client_local_old_output (lio:tftp_client_endpoint_local_io)
  : Ghost.erased TCP.bytes =
  lio.tlo_old_output

(* ───────────────────────────────────────────────────────────────────────────
   pe_prepare_local — Client_start: output = tef_ack, frame_pre = emp
   ─────────────────────────────────────────────────────────────────────────── *)

fn tftp_client_prepare_local
  (i:CC.tftp_client_impl)
  (cfg:tftp_client_config)
  (frame:tftp_client_endpoint_frame)
  (ch:TCP.channel)
  (ev:TP.tftp_client_local)
  (local_frame:CC.tftp_client_local_frame)
  (received:Ghost.erased TCP.bytes)
  (sent:Ghost.erased TCP.bytes)
  (st:Ghost.erased TP.tftp_client_state)
requires
  tftp_client_action_frame i cfg frame (Ghost.reveal st) (PE.EndpointLocal ev local_frame) **
  tftp_client_io_ready i ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st)
returns lio:tftp_client_endpoint_local_io
ensures
  tftp_client_local_io_continuation i ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) ev lio **
  PE.local_output_buffer
    (tftp_client_local_output lio)
    (tftp_client_local_output_len lio)
    (Ghost.reveal (tftp_client_local_old_output lio)) **
  CC.tftp_client_local_frame_pre
    ev
    local_frame
    (Ghost.reveal st)
    (tftp_client_local_output lio)
    (tftp_client_local_output_len lio)
    (Ghost.reveal (tftp_client_local_old_output lio)) **
  tftp_client_local_continuation i cfg frame (Ghost.reveal st) ev local_frame
{
  unfold (tftp_client_action_frame i cfg frame (Ghost.reveal st) (PE.EndpointLocal ev local_frame));
  unfold (tftp_client_frame_ready i cfg frame (Ghost.reveal st));
  unfold (tftp_client_io_ready i ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  with raw dg ack_b. _;
  let lio : tftp_client_endpoint_local_io = {
    tlo_output = frame.tef_ack;
    tlo_old_output = Ghost.hide ack_b;
    tlo_raw_received = Ghost.hide raw;
    tlo_dgram_contents = Ghost.hide dg;
  };
  rewrite (TCP.is_channel ch raw (Ghost.reveal sent))
    as (TCP.is_channel ch (Ghost.reveal lio.tlo_raw_received) (Ghost.reveal sent));
  rewrite (pts_to frame.tef_dgram dg)
    as (pts_to frame.tef_dgram (Ghost.reveal lio.tlo_dgram_contents));
  fold (tftp_client_local_io_continuation i ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) ev lio);
  rewrite (pts_to frame.tef_ack ack_b)
    as (pts_to (tftp_client_local_output lio) (Ghost.reveal (tftp_client_local_old_output lio)));
  fold (PE.local_output_buffer
    (tftp_client_local_output lio)
    (tftp_client_local_output_len lio)
    (Ghost.reveal (tftp_client_local_old_output lio)));
  fold (CC.tftp_client_local_frame_pre
    ev
    local_frame
    (Ghost.reveal st)
    (tftp_client_local_output lio)
    (tftp_client_local_output_len lio)
    (Ghost.reveal (tftp_client_local_old_output lio)));
  fold (tftp_client_local_continuation i cfg frame (Ghost.reveal st) ev local_frame);
  lio
}

(* ───────────────────────────────────────────────────────────────────────────
   pe_finish_local_action
   ─────────────────────────────────────────────────────────────────────────── *)

fn tftp_client_finish_local_action
  (i:CC.tftp_client_impl)
  (cfg:tftp_client_config)
  (frame:tftp_client_endpoint_frame)
  (ev:TP.tftp_client_local)
  (local_frame:CC.tftp_client_local_frame)
  (result:CPI.process_result)
  (old_out:Ghost.erased TCP.bytes)
  (out_contents:Ghost.erased TCP.bytes)
  (st0:Ghost.erased TP.tftp_client_state)
  (st1:Ghost.erased TP.tftp_client_state)
  (wire_outputs:Ghost.erased (list tftp_message))
  (local_outputs:Ghost.erased (list unit))
requires
  tftp_client_local_continuation i cfg frame (Ghost.reveal st0) ev local_frame **
  CC.tftp_client_local_frame_post
    ev
    local_frame
    result
    (Ghost.reveal old_out)
    (Ghost.reveal out_contents)
    (Ghost.reveal st0)
    (Ghost.reveal st1)
    (Ghost.reveal wire_outputs)
    (Ghost.reveal local_outputs)
ensures tftp_client_frame_ready i cfg frame (Ghost.reveal st1)
{
  unfold (tftp_client_local_continuation i cfg frame (Ghost.reveal st0) ev local_frame);
  unfold (CC.tftp_client_local_frame_post
    ev
    local_frame
    result
    (Ghost.reveal old_out)
    (Ghost.reveal out_contents)
    (Ghost.reveal st0)
    (Ghost.reveal st1)
    (Ghost.reveal wire_outputs)
    (Ghost.reveal local_outputs));
  fold (tftp_client_frame_ready i cfg frame (Ghost.reveal st1))
}

(* ───────────────────────────────────────────────────────────────────────────
   pe_finish_local_io — write the (empty) output of Client_start
   ─────────────────────────────────────────────────────────────────────────── *)

fn tftp_client_finish_local_io
  (i:CC.tftp_client_impl)
  (ch:TCP.channel)
  (frame:tftp_client_endpoint_frame)
  (lio:tftp_client_endpoint_local_io)
  (ev:TP.tftp_client_local)
  (result:CPI.process_result)
  (received0:Ghost.erased TCP.bytes)
  (sent0:Ghost.erased TCP.bytes)
  (st0:Ghost.erased TP.tftp_client_state)
  (received1:Ghost.erased TCP.bytes)
  (sent1:Ghost.erased TCP.bytes)
  (st1:Ghost.erased TP.tftp_client_state)
  (out_contents:Ghost.erased TCP.bytes)
  (wire_outputs:Ghost.erased (list tftp_message))
  (local_outputs:Ghost.erased (list unit))
requires
  tftp_client_local_io_continuation i ch frame (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) ev lio **
  pts_to (tftp_client_local_output lio) (Ghost.reveal out_contents) **
  pure (
    CPI.local_process_correct
      (CC.tftp_client_protocol_implementation.CPI.pi_system i)
      ev
      (Ghost.reveal (tftp_client_local_old_output lio))
      (Ghost.reveal out_contents)
      (tftp_client_local_output_len lio)
      (Ghost.reveal received0)
      (Ghost.reveal sent0)
      (Ghost.reveal st0)
      result
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1)
      (Ghost.reveal wire_outputs)
      (Ghost.reveal local_outputs))
ensures tftp_client_io_ready i ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1)
{
  unfold (tftp_client_local_io_continuation i ch frame (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) ev lio);
  CPI.lemma_local_process_sent_output_prefix
    (CC.tftp_client_protocol_implementation.CPI.pi_system i)
    ev
    (Ghost.reveal (tftp_client_local_old_output lio))
    (Ghost.reveal out_contents)
    (tftp_client_local_output_len lio)
    (Ghost.reveal received0)
    (Ghost.reveal sent0)
    (Ghost.reveal st0)
    result
    (Ghost.reveal received1)
    (Ghost.reveal sent1)
    (Ghost.reveal st1)
    (Ghost.reveal wire_outputs)
    (Ghost.reveal local_outputs);
  assert (pure (SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)));
  let nwritten = TCP.write ch (tftp_client_local_output lio) result.CPI.process_produced_len;
  assert (pure (nwritten == result.CPI.process_produced_len));
  rewrite
    (TCP.is_channel
      ch
      (Ghost.reveal lio.tlo_raw_received)
      (Seq.append
        (Ghost.reveal sent0)
        (if SZ.v nwritten <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v nwritten)
         else Seq.create 0 0uy)))
    as
    (TCP.is_channel
      ch
      (Ghost.reveal lio.tlo_raw_received)
      (Seq.append
        (Ghost.reveal sent0)
        (if SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v result.CPI.process_produced_len)
         else Seq.create 0 0uy)));
  assert (pure (Seq.equal
    (Ghost.reveal sent1)
    (Seq.append
      (Ghost.reveal sent0)
      (CPI.output_prefix (Ghost.reveal out_contents) result.CPI.process_produced_len))));
  rewrite
    (TCP.is_channel
      ch
      (Ghost.reveal lio.tlo_raw_received)
      (Seq.append
        (Ghost.reveal sent0)
        (if SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v result.CPI.process_produced_len)
         else Seq.create 0 0uy)))
    as
    (TCP.is_channel ch (Ghost.reveal lio.tlo_raw_received) (Ghost.reveal sent1));
  rewrite (pts_to (tftp_client_local_output lio) (Ghost.reveal out_contents))
    as (pts_to frame.tef_ack (Ghost.reveal out_contents));
  fold (tftp_client_io_ready i ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1))
}

(* ───────────────────────────────────────────────────────────────────────────
   The 28-field endpoint instance
   ─────────────────────────────────────────────────────────────────────────── *)

let tftp_client_protocol_endpoint
  : PE.protocol_endpoint
      CC.tftp_client_impl
      TP.tftp_client_state
      tftp_message
      TP.tftp_client_local
      unit
      CC.tftp_client_protocol_implementation
  =
  {
    PE.pe_config = tftp_client_config;
    PE.pe_frame = tftp_client_endpoint_frame;
    PE.pe_frame_ready = tftp_client_frame_ready;
    PE.pe_io_ready = tftp_client_io_ready;
    PE.pe_action_frame = tftp_client_action_frame;
    PE.pe_network_continuation = tftp_client_network_continuation;
    PE.pe_local_continuation = tftp_client_local_continuation;
    PE.pe_next_action = tftp_client_next_action;
    PE.pe_cancel_action = tftp_client_cancel_action;
    PE.pe_finish_network_action = tftp_client_finish_network_action;
    PE.pe_finish_local_action = tftp_client_finish_local_action;
    PE.pe_network_io = tftp_client_endpoint_network_io;
    PE.pe_network_io_continuation = tftp_client_network_io_continuation;
    PE.pe_network_input = tftp_client_network_input;
    PE.pe_network_input_len = tftp_client_network_input_len;
    PE.pe_network_output = tftp_client_network_output;
    PE.pe_network_output_len = tftp_client_network_output_len;
    PE.pe_network_input_contents = tftp_client_network_input_contents;
    PE.pe_network_old_output = tftp_client_network_old_output;
    PE.pe_prepare_network = tftp_client_prepare_network;
    PE.pe_finish_network_io = tftp_client_finish_network_io;
    PE.pe_local_io = tftp_client_endpoint_local_io;
    PE.pe_local_io_continuation = tftp_client_local_io_continuation;
    PE.pe_local_output = tftp_client_local_output;
    PE.pe_local_output_len = tftp_client_local_output_len;
    PE.pe_local_old_output = tftp_client_local_old_output;
    PE.pe_prepare_local = tftp_client_prepare_local;
    PE.pe_finish_local_io = tftp_client_finish_local_io;
  }
