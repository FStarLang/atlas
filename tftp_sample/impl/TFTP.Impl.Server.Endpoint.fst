module TFTP.Impl.Server.Endpoint

(**
  TFTP *server* (sender) driver-facing endpoint: a full 28-field instance of
  `Common.ProtocolEndpoint.protocol_endpoint` over the committed dictionary
  `TFTP.Impl.Server.CanonicalProtocol.tftp_server_protocol_implementation`.

  This is the executable scheduling + resource layer that lets the GENERIC
  verified loop `Common.ProtocolDriver.drive_steps` run the sender (no loop is
  written here).  Structural port of `YModem.Impl.Server.Endpoint`, adapted to
  TFTP:

    * `server_plan_ok cfg st` couples a concrete send-plan cursor (blocks sent
      so far == `L.length st.tss_sent`) and a started flag (== 1uy iff
      `Some? st.tss_filename`) to the ghost ARQ state: `tss_sent`/`tss_pending`
      are the low/high `Plan.blocks_of` split at the cursor;
    * `pe_next_action` reads the status cell + started + cursor and schedules
         not started                    -> Server_start
         status 0uy, cursor < nblocks   -> Server_send (DATA #(cursor+1))
         status 0uy, cursor == nblocks  -> Server_complete (no EOT: the short
                                           final block ends the transfer)
         status 1uy (block outstanding) -> EndpointNeedInput (await the ACK)
         status 2uy (completed)         -> EndpointDone
         status 3uy (aborted)           -> EndpointFailed;
    * blocks are UNPADDED and variable-length (`min 512 (nbytes - c*512)`, so an
      exact multiple of 512 ends with a 0-byte block).  The local frame's
      payload buffer and the local output must have exactly the block's length
      (resp. 4 + that length), so `pe_next_action` lends the prefix
      `blk[0..len)` of the 512-byte payload scratch as the payload buffer and
      `pe_prepare_local` lends `out[0..4+len)` of the 516-byte output buffer as
      the output; the masked remainders are kept in the continuations and the
      views are joined back by `pe_finish_local_action` / `pe_finish_local_io`;
    * `pe_prepare_local` (Server_send) copies block `cursor` out of the file
      and proves it is `hd pending`; `pe_finish_local_action` increments the
      cursor and re-proves the coupling at cursor+1 via `Plan.lemma_send_shift`;
    * `pe_prepare_network` reads one 4-byte ACK datagram.

  Tier-1 simplification (lossless cooperative peer): `Server_timeout` and a
  local `Server_abort` are never scheduled (dead branches).

  Extracted to C by Custard (which monomorphises the dictionary away) as part
  of the runner `tftp_server_send` in `TFTP.Impl.Server.Socket`.
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
module U16 = FStar.UInt16
module Vec = Pulse.Lib.Vec
module R = Pulse.Lib.Reference
module AC = Pulse.Lib.Array.Core
module L = FStar.List.Tot
module FT = Common.FileTransfer

module TP = TFTP.Protocol
module CC = TFTP.Impl.Server.CanonicalProtocol
module Log = TFTP.Impl.Server.Log
module Plan = TFTP.Impl.Server.Plan

open TFTP.Wire

#set-options "--fuel 1 --ifuel 1 --z3rlimit 10"

(* ───────────────────────────────────────────────────────────────────────────
   Endpoint config (§ pe_config) — the concrete send plan
   ─────────────────────────────────────────────────────────────────────────── *)

(* The file, its byte length and its block count are the runtime fields; the
   byte contents, the block count as a nat and the file name are
   specification-only. *)
noeq
type tftp_server_config = {
  scfg_file       : Vec.vec U8.t;              // the file bytes (scfg_nbytes_sz)
  scfg_contents   : Ghost.erased TCP.bytes;    // == the pts_to value of scfg_file
  scfg_nbytes_sz  : SZ.t;                      // file length
  scfg_nblocks    : Ghost.erased nat;          // nbytes/512 + 1 blocks
  scfg_nblocks_sz : SZ.t;                      // == scfg_nblocks, for runtime comparison
  scfg_filename   : Ghost.erased TCP.bytes;    // file name
}

let scfg_wf (cfg:tftp_server_config) : prop =
  Seq.length cfg.scfg_contents == SZ.v cfg.scfg_nbytes_sz /\
  Ghost.reveal cfg.scfg_nblocks == SZ.v cfg.scfg_nblocks_sz /\
  Ghost.reveal cfg.scfg_nblocks == SZ.v cfg.scfg_nbytes_sz / 512 + 1 /\
  Ghost.reveal cfg.scfg_nblocks <= 65534

(* The whole plan the sender queues at Server_start. *)
let plan_of (cfg:tftp_server_config) : Ghost.erased (list TCP.bytes) =
  Ghost.elift2 (fun c n -> Plan.blocks_of c 0 n) cfg.scfg_contents cfg.scfg_nblocks

(* ───────────────────────────────────────────────────────────────────────────
   Endpoint frame (§ pe_frame): the persistent concrete state + I/O buffers
   ─────────────────────────────────────────────────────────────────────────── *)

noeq
type tftp_server_endpoint_frame = {
  sef_cursor  : Vec.vec SZ.t;   // single cell: blocks sent so far (0..nblocks)
  sef_started : Vec.vec U8.t;   // single cell: 1uy iff Server_start has fired
  sef_blk     : array U8.t;     // 512-byte payload scratch (prefix lent as tslf_buf)
  sef_tsnf    : array U8.t;     // 516-byte scratch handed to process_network
  sef_out     : array U8.t;     // 516-byte output buffer (DATA packets)
  sef_in      : array U8.t;     // 4-byte ACK input
}

(* ───────────────────────────────────────────────────────────────────────────
   Prefix views: lend `buf[0..n)` (of an m-byte buffer) as an exact-length
   array, keeping the masked remainder aside.
   ─────────────────────────────────────────────────────────────────────────── *)

let prefix_view (parent v:array U8.t) (n:nat) : prop =
  if n <= AC.length parent then v == AC.gsub parent 0 n else False

let prefix_rest (buf:array U8.t) (m:nat) (n:SZ.t) : slprop =
  exists* (s:Seq.seq (option U8.t)).
    AC.pts_to_mask buf s (fun k -> ~(k < SZ.v n)) **
    pure (
      Seq.length s == m /\
      (forall (k:nat). k < Seq.length s ==> Some? (Seq.index s k)))

fn take_prefix (buf:array U8.t) (m:Ghost.erased nat) (n:SZ.t) (#c:Ghost.erased (Seq.seq U8.t))
requires
  pts_to buf c **
  pure (Seq.length c == Ghost.reveal m /\ SZ.v n <= Ghost.reveal m)
returns v:array U8.t
ensures exists* (pc:Seq.seq U8.t).
  pts_to v pc **
  prefix_rest buf m n **
  pure (Seq.length pc == SZ.v n /\ prefix_view buf v (SZ.v n))
{
  pts_to_len buf;
  to_mask buf;
  let v = AC.sub buf 0sz (SZ.v n);
  AC.mask_mext buf (fun k -> ~(k < SZ.v n));
  fold (prefix_rest buf m n);
  from_mask v;
  pts_to_len v;
  v
}

ghost
fn give_back_prefix
  (buf:array U8.t) (m:Ghost.erased nat) (n:SZ.t) (v:array U8.t)
  (#pc:Ghost.erased (Seq.seq U8.t))
requires
  pts_to v pc **
  prefix_rest buf m n **
  pure (Seq.length pc == SZ.v n /\ prefix_view buf v (SZ.v n))
ensures exists* (c:Seq.seq U8.t).
  pts_to buf c **
  pure (Seq.length c == Ghost.reveal m)
{
  unfold (prefix_rest buf m n);
  with s. _;
  to_mask v;
  with sv. _;
  rewrite (AC.pts_to_mask v sv (fun _ -> True))
    as (AC.pts_to_mask (AC.gsub buf 0 (SZ.v n)) sv (fun _ -> True));
  AC.return_sub buf #1.0R #s #sv #(fun k -> ~(k < SZ.v n)) #(fun _ -> True) #0 #(SZ.v n);
  from_mask buf;
}

(* ───────────────────────────────────────────────────────────────────────────
   THE COUPLING INVARIANT
   ─────────────────────────────────────────────────────────────────────────── *)

(* Keyed on `st.tss_filename`:
     * None (not started) ⟹ st is exactly the initial state;
     * Some fn (started) and InProgress ⟹ the file name matches the config, the
       cursor `L.length tss_sent` is in range, and `tss_sent`/`tss_pending` are
       the low/high `blocks_of` split at the cursor. *)
unfold
let server_plan_ok (cfg:tftp_server_config) (st:TP.tftp_server_state) : prop =
  match st.TP.tss_filename with
  | None -> st == TP.tftp_server_initial
  | Some fnm ->
    st.TP.tss_status == FT.FT_InProgress ==>
      (fnm == Ghost.reveal cfg.scfg_filename /\
       L.length st.TP.tss_sent <= cfg.scfg_nblocks /\
       st.TP.tss_sent == Plan.blocks_of cfg.scfg_contents 0 (L.length st.TP.tss_sent) /\
       st.TP.tss_pending == Plan.blocks_of cfg.scfg_contents (L.length st.TP.tss_sent) cfg.scfg_nblocks)

unfold
let started_of (b:U8.t) : bool = (b = 1uy)

(* The concrete cursor/started cells agree with the ghost state. *)
unfold
let cells_ok (cv:Seq.seq SZ.t) (bv:Seq.seq U8.t) (st:TP.tftp_server_state) : prop =
  Seq.length cv == 1 /\ Seq.length bv == 1 /\
  (Seq.index bv 0 == 0uy \/ Seq.index bv 0 == 1uy) /\
  (started_of (Seq.index bv 0) <==> Some? st.TP.tss_filename) /\
  SZ.v (Seq.index cv 0) == L.length st.TP.tss_sent

(* ───────────────────────────────────────────────────────────────────────────
   Persistent slprops (§ pe_frame_ready, pe_io_ready)
   ─────────────────────────────────────────────────────────────────────────── *)

(* frame_ready [STATE-DEPENDENT]: owns the two cells, the file and the two
   scratches, and carries the coupling + cell agreement. *)
let tftp_server_frame_ready
  (_i:CC.tftp_server_impl)
  (cfg:tftp_server_config)
  (frame:tftp_server_endpoint_frame)
  (st:TP.tftp_server_state)
  : slprop =
  exists* (cv:Seq.seq SZ.t) (bv:Seq.seq U8.t) (blkd:Seq.seq U8.t) (tsnfd:Seq.seq U8.t).
    Vec.pts_to frame.sef_cursor cv **
    Vec.pts_to frame.sef_started bv **
    Vec.pts_to cfg.scfg_file cfg.scfg_contents **
    pts_to frame.sef_blk blkd **
    pts_to frame.sef_tsnf tsnfd **
    pure (Seq.length blkd == 512 /\ Seq.length tsnfd == 516 /\
          scfg_wf cfg /\ cells_ok cv bv st /\ server_plan_ok cfg st)

(* io_ready [STATE-INDEPENDENT]: owns the channel + the 516-byte output + the
   4-byte input.  The raw received history is existential. *)
let tftp_server_io_ready
  (_i:CC.tftp_server_impl)
  (ch:TCP.channel)
  (frame:tftp_server_endpoint_frame)
  (_received:TCP.bytes)
  (sent:TCP.bytes)
  (_st:TP.tftp_server_state)
  : slprop =
  exists* (raw:TCP.bytes) (outd:Seq.seq U8.t) (ind:Seq.seq U8.t).
    TCP.is_channel ch raw sent **
    pts_to frame.sef_out outd **
    pts_to frame.sef_in ind **
    pure (Seq.length outd == 516 /\ Seq.length ind == 4)

(* ───────────────────────────────────────────────────────────────────────────
   Per-event scheduling facts (consumed by prepare_local) and continuation facts
   (consumed by finish_local_action).
   ─────────────────────────────────────────────────────────────────────────── *)

unfold
let server_local_ready (cfg:tftp_server_config) (ev:TP.tftp_server_local)
                       (lf:CC.tftp_server_local_frame)
                       (st:TP.tftp_server_state) : prop =
  match ev with
  | TP.Server_start filename plan ->
    st == TP.tftp_server_initial /\
    Ghost.reveal filename == Ghost.reveal cfg.scfg_filename /\
    Ghost.reveal plan == Ghost.reveal (plan_of cfg)
  | TP.Server_send ->
    Some? st.TP.tss_filename /\ st.TP.tss_status == FT.FT_InProgress /\
    L.length st.TP.tss_sent == st.TP.tss_acked /\
    L.length st.TP.tss_sent < cfg.scfg_nblocks /\
    U16.v lf.CC.tslf_blk == L.length st.TP.tss_sent + 1 /\
    SZ.v lf.CC.tslf_len ==
      Seq.length (Plan.block cfg.scfg_contents (L.length st.TP.tss_sent))
  | TP.Server_complete ->
    Some? st.TP.tss_filename /\ st.TP.tss_status == FT.FT_InProgress /\
    L.length st.TP.tss_sent == st.TP.tss_acked /\
    L.length st.TP.tss_sent == cfg.scfg_nblocks
  | TP.Server_abort -> False
  | TP.Server_timeout -> False

unfold
let server_local_cont (cfg:tftp_server_config) (ev:TP.tftp_server_local)
                      (st0:TP.tftp_server_state) : prop =
  match ev with
  | TP.Server_start filename plan ->
    st0 == TP.tftp_server_initial /\
    Ghost.reveal filename == Ghost.reveal cfg.scfg_filename /\
    Ghost.reveal plan == Ghost.reveal (plan_of cfg)
  | TP.Server_send ->
    Some? st0.TP.tss_filename /\ st0.TP.tss_status == FT.FT_InProgress /\
    L.length st0.TP.tss_sent < cfg.scfg_nblocks
  | TP.Server_complete -> Some? st0.TP.tss_filename
  | TP.Server_abort -> False
  | TP.Server_timeout -> False

(* ───────────────────────────────────────────────────────────────────────────
   Action frame (§ pe_action_frame) and action continuations
   ─────────────────────────────────────────────────────────────────────────── *)

(* For a local event the payload view `blk[0..tslf_len)` is already lent out
   (it is the local frame's buffer), so the action frame owns the view and the
   masked remainder instead of the whole 512-byte scratch. *)
let tftp_server_action_frame
  (i:CC.tftp_server_impl)
  (cfg:tftp_server_config)
  (frame:tftp_server_endpoint_frame)
  (st:TP.tftp_server_state)
  (action:PE.endpoint_action
    CC.tftp_server_network_frame
    TP.tftp_server_local
    CC.tftp_server_local_frame)
  : slprop =
  match action with
  | PE.EndpointNeedInput nf ->
    tftp_server_frame_ready i cfg frame st **
    pure (nf.CC.tsnf_buf == frame.sef_tsnf /\ Some? st.TP.tss_filename)
  | PE.EndpointLocal ev lf ->
    exists* (cv:Seq.seq SZ.t) (bv:Seq.seq U8.t) (pc:Seq.seq U8.t) (tsnfd:Seq.seq U8.t).
      Vec.pts_to frame.sef_cursor cv **
      Vec.pts_to frame.sef_started bv **
      Vec.pts_to cfg.scfg_file cfg.scfg_contents **
      pts_to lf.CC.tslf_buf pc **
      prefix_rest frame.sef_blk 512 lf.CC.tslf_len **
      pts_to frame.sef_tsnf tsnfd **
      pure (Seq.length pc == SZ.v lf.CC.tslf_len /\ SZ.v lf.CC.tslf_len <= 512 /\
            prefix_view frame.sef_blk lf.CC.tslf_buf (SZ.v lf.CC.tslf_len) /\
            Seq.length tsnfd == 516 /\
            scfg_wf cfg /\ cells_ok cv bv st /\ server_plan_ok cfg st /\
            server_local_ready cfg ev lf st)
  | PE.EndpointDone
  | PE.EndpointFailed ->
    tftp_server_frame_ready i cfg frame st

(* Network continuation: owns cursor+started+file+sef_blk (NOT sef_tsnf, which
   network_frame_pre owns). *)
let tftp_server_network_continuation
  (_i:CC.tftp_server_impl)
  (cfg:tftp_server_config)
  (frame:tftp_server_endpoint_frame)
  (st:TP.tftp_server_state)
  (nf:CC.tftp_server_network_frame)
  : slprop =
  exists* (cv:Seq.seq SZ.t) (bv:Seq.seq U8.t) (blkd:Seq.seq U8.t).
    Vec.pts_to frame.sef_cursor cv **
    Vec.pts_to frame.sef_started bv **
    Vec.pts_to cfg.scfg_file cfg.scfg_contents **
    pts_to frame.sef_blk blkd **
    pure (Seq.length blkd == 512 /\ scfg_wf cfg /\
          cells_ok cv bv st /\ server_plan_ok cfg st /\
          Some? st.TP.tss_filename /\
          nf.CC.tsnf_buf == frame.sef_tsnf)

(* Local continuation: owns cursor+started+file+sef_tsnf and the masked
   remainder of sef_blk (the payload view is owned by local_frame_pre). *)
let tftp_server_local_continuation
  (_i:CC.tftp_server_impl)
  (cfg:tftp_server_config)
  (frame:tftp_server_endpoint_frame)
  (st:TP.tftp_server_state)
  (ev:TP.tftp_server_local)
  (lf:CC.tftp_server_local_frame)
  : slprop =
  exists* (cv:Seq.seq SZ.t) (bv:Seq.seq U8.t) (tsnfd:Seq.seq U8.t).
    Vec.pts_to frame.sef_cursor cv **
    Vec.pts_to frame.sef_started bv **
    Vec.pts_to cfg.scfg_file cfg.scfg_contents **
    pts_to frame.sef_tsnf tsnfd **
    prefix_rest frame.sef_blk 512 lf.CC.tslf_len **
    pure (Seq.length tsnfd == 516 /\ scfg_wf cfg /\
          cells_ok cv bv st /\ server_plan_ok cfg st /\
          prefix_view frame.sef_blk lf.CC.tslf_buf (SZ.v lf.CC.tslf_len) /\
          server_local_cont cfg ev st)

(* ───────────────────────────────────────────────────────────────────────────
   Network I/O carrier (§ pe_network_io) + continuation + accessors
   ─────────────────────────────────────────────────────────────────────────── *)

noeq
type tftp_server_endpoint_network_io = {
  sni_input          : array U8.t;
  sni_input_len      : SZ.t;
  sni_output         : array U8.t;
  sni_input_contents : Ghost.erased TCP.bytes;
  sni_old_output     : Ghost.erased TCP.bytes;
  sni_raw_received   : Ghost.erased TCP.bytes;
}

let tftp_server_network_io_continuation
  (_i:CC.tftp_server_impl)
  (ch:TCP.channel)
  (frame:tftp_server_endpoint_frame)
  (_received:TCP.bytes)
  (sent:TCP.bytes)
  (_st:TP.tftp_server_state)
  (nio:tftp_server_endpoint_network_io)
  : slprop =
  TCP.is_channel ch (Ghost.reveal nio.sni_raw_received) sent **
  pure (
    nio.sni_input == frame.sef_in /\
    nio.sni_output == frame.sef_out /\
    nio.sni_input_len == 4sz /\
    Seq.length (Ghost.reveal nio.sni_old_output) == 516 /\
    Seq.length (Ghost.reveal nio.sni_input_contents) == 4)

let tftp_server_network_input (nio:tftp_server_endpoint_network_io) : array U8.t =
  nio.sni_input
let tftp_server_network_input_len (nio:tftp_server_endpoint_network_io) : SZ.t =
  nio.sni_input_len
let tftp_server_network_output (nio:tftp_server_endpoint_network_io) : array U8.t =
  nio.sni_output
let tftp_server_network_output_len (_nio:tftp_server_endpoint_network_io) : SZ.t =
  516sz
let tftp_server_network_input_contents (nio:tftp_server_endpoint_network_io)
  : Ghost.erased TCP.bytes = nio.sni_input_contents
let tftp_server_network_old_output (nio:tftp_server_endpoint_network_io)
  : Ghost.erased TCP.bytes = nio.sni_old_output

(* ───────────────────────────────────────────────────────────────────────────
   pe_next_action — read status cell + started + cursor and schedule
   ─────────────────────────────────────────────────────────────────────────── *)

(* Lend `blk[0..len)` as the payload buffer of a local event. *)
fn lend_local
  (i:CC.tftp_server_impl)
  (cfg:tftp_server_config)
  (frame:tftp_server_endpoint_frame)
  (st:Ghost.erased TP.tftp_server_state)
  (ev:TP.tftp_server_local)
  (blkno:U16.t)
  (len:SZ.t)
requires
  tftp_server_frame_ready i cfg frame (Ghost.reveal st) **
  pure (SZ.v len <= 512 /\
        server_local_ready cfg ev
          ({ CC.tslf_buf = frame.sef_blk; CC.tslf_blk = blkno; CC.tslf_len = len })
          (Ghost.reveal st))
returns lf:CC.tftp_server_local_frame
ensures
  tftp_server_action_frame i cfg frame (Ghost.reveal st) (PE.EndpointLocal ev lf)
{
  unfold (tftp_server_frame_ready i cfg frame (Ghost.reveal st));
  with cv bv blkd tsnfd. _;
  let v = take_prefix frame.sef_blk 512 len;
  with pc. _;
  let lf : CC.tftp_server_local_frame = { CC.tslf_buf = v; CC.tslf_blk = blkno; CC.tslf_len = len };
  rewrite (pts_to v pc) as (pts_to lf.CC.tslf_buf pc);
  rewrite (prefix_rest frame.sef_blk 512 len) as (prefix_rest frame.sef_blk 512 lf.CC.tslf_len);
  fold (tftp_server_action_frame i cfg frame (Ghost.reveal st) (PE.EndpointLocal ev lf));
  lf
}

fn tftp_server_next_action
  (i:CC.tftp_server_impl)
  (cfg:tftp_server_config)
  (frame:tftp_server_endpoint_frame)
  (received:Ghost.erased TCP.bytes)
  (sent:Ghost.erased TCP.bytes)
  (st:Ghost.erased TP.tftp_server_state)
requires
  CC.tftp_server_inv i (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) **
  tftp_server_frame_ready i cfg frame (Ghost.reveal st)
returns action:PE.endpoint_action
  CC.tftp_server_network_frame
  TP.tftp_server_local
  CC.tftp_server_local_frame
ensures
  CC.tftp_server_inv i (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) **
  tftp_server_action_frame i cfg frame (Ghost.reveal st) action **
  pure (PE.action_not_internal CC.tftp_server_protocol_implementation action)
{
  unfold (CC.tftp_server_inv i (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  with svs evs. _;
  let s = Vec.op_Dot_Lparen_Rparen i.CC.status 0sz;
  fold (CC.tftp_server_inv i (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  unfold (tftp_server_frame_ready i cfg frame (Ghost.reveal st));
  with cv bv blkd tsnfd. _;
  let b = Vec.op_Dot_Lparen_Rparen frame.sef_started 0sz;
  let c = Vec.op_Dot_Lparen_Rparen frame.sef_cursor 0sz;
  fold (tftp_server_frame_ready i cfg frame (Ghost.reveal st));
  if (b = 0uy) {
    (* not started → Server_start (filename None ⟹ st == initial) *)
    let ev = TP.Server_start cfg.scfg_filename (plan_of cfg);
    let lf = lend_local i cfg frame st ev 0us 0sz;
    PE.EndpointLocal ev lf
  } else if (s = 0uy) {
    if (SZ.lt c cfg.scfg_nblocks_sz) {
      (* block c is DATA #(c+1); its length is min 512 (nbytes - c*512) *)
      Plan.block_offset_le cfg.scfg_contents cfg.scfg_nblocks (SZ.v c);
      FStar.SizeT.fits_lte (SZ.v c * 512) (SZ.v cfg.scfg_nbytes_sz);
      let off = SZ.mul c 512sz;
      let rem = SZ.sub cfg.scfg_nbytes_sz off;
      let len = if (SZ.lt rem 512sz) { (rem <: SZ.t) } else { 512sz };
      Plan.block_len_eq cfg.scfg_contents (SZ.v c);
      FStar.Math.Lemmas.small_mod (SZ.v c + 1) (pow2 32);
      FStar.Math.Lemmas.small_mod (SZ.v c + 1) (pow2 16);
      let blkno = FStar.Int.Cast.uint32_to_uint16 (SZ.sizet_to_uint32 (SZ.add c 1sz));
      let lf = lend_local i cfg frame st TP.Server_send blkno len;
      PE.EndpointLocal TP.Server_send lf
    } else {
      (* all blocks sent and acked → complete (no EOT) *)
      let lf = lend_local i cfg frame st TP.Server_complete 0us 0sz;
      PE.EndpointLocal TP.Server_complete lf
    }
  } else if (s = 1uy) {
    (* one block outstanding → await its ACK *)
    let nf : CC.tftp_server_network_frame = { CC.tsnf_buf = frame.sef_tsnf; CC.tsnf_blk = 0us };
    fold (tftp_server_action_frame i cfg frame (Ghost.reveal st) (PE.EndpointNeedInput nf));
    PE.EndpointNeedInput nf
  } else if (s = 2uy) {
    fold (tftp_server_action_frame i cfg frame (Ghost.reveal st) PE.EndpointDone);
    PE.EndpointDone
  } else {
    fold (tftp_server_action_frame i cfg frame (Ghost.reveal st) PE.EndpointFailed);
    PE.EndpointFailed
  }
}

(* ───────────────────────────────────────────────────────────────────────────
   pe_cancel_action
   ─────────────────────────────────────────────────────────────────────────── *)

fn tftp_server_cancel_action
  (i:CC.tftp_server_impl)
  (cfg:tftp_server_config)
  (frame:tftp_server_endpoint_frame)
  (st:Ghost.erased TP.tftp_server_state)
  (action:PE.endpoint_action
    CC.tftp_server_network_frame
    TP.tftp_server_local
    CC.tftp_server_local_frame)
requires tftp_server_action_frame i cfg frame (Ghost.reveal st) action
ensures tftp_server_frame_ready i cfg frame (Ghost.reveal st)
{
  match action {
    PE.EndpointNeedInput nf -> {
      unfold (tftp_server_action_frame i cfg frame (Ghost.reveal st) (PE.EndpointNeedInput nf))
    }
    PE.EndpointLocal ev lf -> {
      unfold (tftp_server_action_frame i cfg frame (Ghost.reveal st) (PE.EndpointLocal ev lf));
      with cv bv pc tsnfd. _;
      give_back_prefix frame.sef_blk 512 lf.CC.tslf_len lf.CC.tslf_buf;
      fold (tftp_server_frame_ready i cfg frame (Ghost.reveal st))
    }
    PE.EndpointDone -> {
      unfold (tftp_server_action_frame i cfg frame (Ghost.reveal st) PE.EndpointDone)
    }
    PE.EndpointFailed -> {
      unfold (tftp_server_action_frame i cfg frame (Ghost.reveal st) PE.EndpointFailed)
    }
  }
}

(* ───────────────────────────────────────────────────────────────────────────
   pe_prepare_network — read one 4-byte ACK datagram into sef_in
   ─────────────────────────────────────────────────────────────────────────── *)

fn tftp_server_prepare_network
  (i:CC.tftp_server_impl)
  (cfg:tftp_server_config)
  (frame:tftp_server_endpoint_frame)
  (ch:TCP.channel)
  (nf:CC.tftp_server_network_frame)
  (received:Ghost.erased TCP.bytes)
  (sent:Ghost.erased TCP.bytes)
  (st:Ghost.erased TP.tftp_server_state)
requires
  tftp_server_action_frame i cfg frame (Ghost.reveal st) (PE.EndpointNeedInput nf) **
  tftp_server_io_ready i ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st)
returns nio:tftp_server_endpoint_network_io
ensures
  tftp_server_network_io_continuation i ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) nio **
  PE.network_buffers
    (tftp_server_network_input nio)
    (tftp_server_network_input_len nio)
    (tftp_server_network_output nio)
    (tftp_server_network_output_len nio)
    (Ghost.reveal (tftp_server_network_input_contents nio))
    (Ghost.reveal (tftp_server_network_old_output nio)) **
  CC.tftp_server_network_frame_pre
    nf
    (tftp_server_network_input nio)
    (tftp_server_network_input_len nio)
    (tftp_server_network_output nio)
    (tftp_server_network_output_len nio)
    (Ghost.reveal (tftp_server_network_input_contents nio))
    (Ghost.reveal (tftp_server_network_old_output nio)) **
  tftp_server_network_continuation i cfg frame (Ghost.reveal st) nf **
  pure (
    CPI.buffers_wf
      (Ghost.reveal (tftp_server_network_input_contents nio))
      (tftp_server_network_input_len nio)
      (Ghost.reveal (tftp_server_network_old_output nio))
      (tftp_server_network_output_len nio))
{
  unfold (tftp_server_action_frame i cfg frame (Ghost.reveal st) (PE.EndpointNeedInput nf));
  unfold (tftp_server_frame_ready i cfg frame (Ghost.reveal st));
  with cv bv blkd tsnfd. _;
  unfold (tftp_server_io_ready i ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  with raw outd ind. _;
  let nread = TCP.read_full ch frame.sef_in 4sz;
  with ind2 chunk. _;
  let nio : tftp_server_endpoint_network_io = {
    sni_input = frame.sef_in;
    sni_input_len = 4sz;
    sni_output = frame.sef_out;
    sni_input_contents = Ghost.hide ind2;
    sni_old_output = Ghost.hide outd;
    sni_raw_received = Ghost.hide (Seq.append raw chunk);
  };
  rewrite (TCP.is_channel ch (Seq.append raw chunk) (Ghost.reveal sent))
    as (TCP.is_channel ch (Ghost.reveal nio.sni_raw_received) (Ghost.reveal sent));
  fold (tftp_server_network_io_continuation i ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) nio);
  rewrite (pts_to frame.sef_in ind2)
    as (pts_to (tftp_server_network_input nio) (Ghost.reveal (tftp_server_network_input_contents nio)));
  rewrite (pts_to frame.sef_out outd)
    as (pts_to (tftp_server_network_output nio) (Ghost.reveal (tftp_server_network_old_output nio)));
  fold (PE.network_buffers
    (tftp_server_network_input nio)
    (tftp_server_network_input_len nio)
    (tftp_server_network_output nio)
    (tftp_server_network_output_len nio)
    (Ghost.reveal (tftp_server_network_input_contents nio))
    (Ghost.reveal (tftp_server_network_old_output nio)));
  assert (pure (nf.CC.tsnf_buf == frame.sef_tsnf));
  rewrite (pts_to frame.sef_tsnf tsnfd)
    as (pts_to nf.CC.tsnf_buf tsnfd);
  fold (CC.tftp_server_network_frame_pre
    nf
    (tftp_server_network_input nio)
    (tftp_server_network_input_len nio)
    (tftp_server_network_output nio)
    (tftp_server_network_output_len nio)
    (Ghost.reveal (tftp_server_network_input_contents nio))
    (Ghost.reveal (tftp_server_network_old_output nio)));
  fold (tftp_server_network_continuation i cfg frame (Ghost.reveal st) nf);
  nio
}

(* ───────────────────────────────────────────────────────────────────────────
   pe_finish_network_action — re-establish the coupling (unchanged cells)
   ─────────────────────────────────────────────────────────────────────────── *)

(* The coupling + cell agreement survive every network transition (noop / ack
   / abort): all keep filename, sent and pending; ack only bumps `acked`, abort
   flips the status (making the InProgress guard false). *)
let network_coupling_preserved
  (cfg:tftp_server_config) (cv:Seq.seq SZ.t) (bv:Seq.seq U8.t)
  (st0 st1:TP.tftp_server_state)
  : Lemma
    (requires
      cells_ok cv bv st0 /\ server_plan_ok cfg st0 /\
      Some? st0.TP.tss_filename /\
      (st1 == st0 \/ st1 == Log.ack_next_state st0 \/ st1 == Log.abort_next_state st0))
    (ensures cells_ok cv bv st1 /\ server_plan_ok cfg st1)
  = ()

fn tftp_server_finish_network_action
  (i:CC.tftp_server_impl)
  (cfg:tftp_server_config)
  (frame:tftp_server_endpoint_frame)
  (nf:CC.tftp_server_network_frame)
  (result:CPI.process_result)
  (input_contents:Ghost.erased TCP.bytes)
  (input_len:SZ.t)
  (old_out:Ghost.erased TCP.bytes)
  (out_contents:Ghost.erased TCP.bytes)
  (st0:Ghost.erased TP.tftp_server_state)
  (st1:Ghost.erased TP.tftp_server_state)
  (consumed:Ghost.erased TCP.bytes)
  (wire_outputs:Ghost.erased (list tftp_message))
  (local_outputs:Ghost.erased (list unit))
requires
  tftp_server_network_continuation i cfg frame (Ghost.reveal st0) nf **
  CC.tftp_server_network_frame_post
    nf result (Ghost.reveal input_contents) input_len
    (Ghost.reveal old_out) (Ghost.reveal out_contents)
    (Ghost.reveal st0) (Ghost.reveal st1)
    (Ghost.reveal consumed) (Ghost.reveal wire_outputs) (Ghost.reveal local_outputs)
ensures tftp_server_frame_ready i cfg frame (Ghost.reveal st1)
{
  unfold (tftp_server_network_continuation i cfg frame (Ghost.reveal st0) nf);
  with cv bv blkd. _;
  unfold (CC.tftp_server_network_frame_post
    nf result (Ghost.reveal input_contents) input_len
    (Ghost.reveal old_out) (Ghost.reveal out_contents)
    (Ghost.reveal st0) (Ghost.reveal st1)
    (Ghost.reveal consumed) (Ghost.reveal wire_outputs) (Ghost.reveal local_outputs));
  with o'. _;
  assert (pure (nf.CC.tsnf_buf == frame.sef_tsnf));
  rewrite (pts_to nf.CC.tsnf_buf o')
    as (pts_to frame.sef_tsnf o');
  network_coupling_preserved cfg cv bv (Ghost.reveal st0) (Ghost.reveal st1);
  fold (tftp_server_frame_ready i cfg frame (Ghost.reveal st1))
}

(* ───────────────────────────────────────────────────────────────────────────
   pe_finish_network_io — write produced bytes, re-establish io_ready
   ─────────────────────────────────────────────────────────────────────────── *)

fn tftp_server_finish_network_io
  (i:CC.tftp_server_impl)
  (ch:TCP.channel)
  (frame:tftp_server_endpoint_frame)
  (nio:tftp_server_endpoint_network_io)
  (result:CPI.process_result)
  (received0:Ghost.erased TCP.bytes)
  (sent0:Ghost.erased TCP.bytes)
  (st0:Ghost.erased TP.tftp_server_state)
  (received1:Ghost.erased TCP.bytes)
  (sent1:Ghost.erased TCP.bytes)
  (st1:Ghost.erased TP.tftp_server_state)
  (out_contents:Ghost.erased TCP.bytes)
  (consumed:Ghost.erased TCP.bytes)
  (wire_outputs:Ghost.erased (list tftp_message))
  (local_outputs:Ghost.erased (list unit))
requires
  tftp_server_network_io_continuation i ch frame (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) nio **
  pts_to (tftp_server_network_input nio) (Ghost.reveal (tftp_server_network_input_contents nio)) **
  pts_to (tftp_server_network_output nio) (Ghost.reveal out_contents) **
  pure (
    CPI.network_process_correct
      (CC.tftp_server_protocol_implementation.CPI.pi_system i)
      (Ghost.reveal (tftp_server_network_input_contents nio))
      (tftp_server_network_input_len nio)
      (Ghost.reveal (tftp_server_network_old_output nio))
      (Ghost.reveal out_contents)
      (tftp_server_network_output_len nio)
      (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0)
      result
      (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1)
      (Ghost.reveal consumed) (Ghost.reveal wire_outputs) (Ghost.reveal local_outputs))
ensures tftp_server_io_ready i ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1)
{
  unfold (tftp_server_network_io_continuation i ch frame (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) nio);
  CPI.lemma_network_process_sent_output_prefix
    (CC.tftp_server_protocol_implementation.CPI.pi_system i)
    (Ghost.reveal (tftp_server_network_input_contents nio))
    (tftp_server_network_input_len nio)
    (Ghost.reveal (tftp_server_network_old_output nio))
    (Ghost.reveal out_contents)
    (tftp_server_network_output_len nio)
    (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0)
    result
    (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1)
    (Ghost.reveal consumed) (Ghost.reveal wire_outputs) (Ghost.reveal local_outputs);
  assert (pure (SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)));
  let nwritten = TCP.write ch (tftp_server_network_output nio) result.CPI.process_produced_len;
  assert (pure (nwritten == result.CPI.process_produced_len));
  rewrite
    (TCP.is_channel ch (Ghost.reveal nio.sni_raw_received)
      (Seq.append (Ghost.reveal sent0)
        (if SZ.v nwritten <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v nwritten)
         else Seq.create 0 0uy)))
    as
    (TCP.is_channel ch (Ghost.reveal nio.sni_raw_received)
      (Seq.append (Ghost.reveal sent0)
        (if SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v result.CPI.process_produced_len)
         else Seq.create 0 0uy)));
  assert (pure (Seq.equal (Ghost.reveal sent1)
    (Seq.append (Ghost.reveal sent0)
      (CPI.output_prefix (Ghost.reveal out_contents) result.CPI.process_produced_len))));
  rewrite
    (TCP.is_channel ch (Ghost.reveal nio.sni_raw_received)
      (Seq.append (Ghost.reveal sent0)
        (if SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v result.CPI.process_produced_len)
         else Seq.create 0 0uy)))
    as
    (TCP.is_channel ch (Ghost.reveal nio.sni_raw_received) (Ghost.reveal sent1));
  rewrite (pts_to (tftp_server_network_output nio) (Ghost.reveal out_contents))
    as (pts_to frame.sef_out (Ghost.reveal out_contents));
  rewrite (pts_to (tftp_server_network_input nio) (Ghost.reveal (tftp_server_network_input_contents nio)))
    as (pts_to frame.sef_in (Ghost.reveal (tftp_server_network_input_contents nio)));
  fold (tftp_server_io_ready i ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1))
}

(* ───────────────────────────────────────────────────────────────────────────
   Local I/O carrier (§ pe_local_io) + continuation + accessors.  The output
   is the exact-length view `out[0..4+len)` of the 516-byte output buffer.
   ─────────────────────────────────────────────────────────────────────────── *)

noeq
type tftp_server_endpoint_local_io = {
  slo_output       : array U8.t;
  slo_output_len   : SZ.t;
  slo_old_output   : Ghost.erased TCP.bytes;
  slo_raw_received : Ghost.erased TCP.bytes;
}

let tftp_server_local_io_continuation
  (_i:CC.tftp_server_impl)
  (ch:TCP.channel)
  (frame:tftp_server_endpoint_frame)
  (_received:TCP.bytes)
  (sent:TCP.bytes)
  (_st:TP.tftp_server_state)
  (_ev:TP.tftp_server_local)
  (lio:tftp_server_endpoint_local_io)
  : slprop =
  exists* (ind:Seq.seq U8.t).
    TCP.is_channel ch (Ghost.reveal lio.slo_raw_received) sent **
    pts_to frame.sef_in ind **
    prefix_rest frame.sef_out 516 lio.slo_output_len **
    pure (
      Seq.length ind == 4 /\
      SZ.v lio.slo_output_len <= 516 /\
      prefix_view frame.sef_out lio.slo_output (SZ.v lio.slo_output_len) /\
      Seq.length (Ghost.reveal lio.slo_old_output) == SZ.v lio.slo_output_len)

let tftp_server_local_output (lio:tftp_server_endpoint_local_io) : array U8.t =
  lio.slo_output
let tftp_server_local_output_len (lio:tftp_server_endpoint_local_io) : SZ.t =
  lio.slo_output_len
let tftp_server_local_old_output (lio:tftp_server_endpoint_local_io)
  : Ghost.erased TCP.bytes = lio.slo_old_output

(* ───────────────────────────────────────────────────────────────────────────
   Block copy helper: dst[0..len) := file[off..off+len)
   ─────────────────────────────────────────────────────────────────────────── *)

fn copy_block
  (file:Vec.vec U8.t)
  (dst:array U8.t)
  (off:SZ.t)
  (len:SZ.t)
  (#contents:Ghost.erased TCP.bytes)
  (#d0:Ghost.erased (Seq.seq U8.t))
requires
  Vec.pts_to file contents ** pts_to dst d0 **
  pure (Seq.length d0 == SZ.v len /\
        SZ.v off + SZ.v len <= Seq.length contents /\
        SZ.fits (SZ.v off + SZ.v len))
returns _:unit
ensures exists* (d1:Seq.seq U8.t).
  Vec.pts_to file contents ** pts_to dst d1 **
  pure (Seq.length d1 == SZ.v len /\
        SZ.v off + SZ.v len <= Seq.length contents /\
        (forall (k:nat). k < SZ.v len ==>
           Seq.index d1 k == Seq.index (Ghost.reveal contents) (SZ.v off + k)))
{
  let mut j = 0sz;
  while (SZ.lt (!j) len)
  invariant exists* (vj:SZ.t) (d:Seq.seq U8.t).
    R.pts_to j vj **
    Vec.pts_to file contents **
    pts_to dst d **
    pure (SZ.v vj <= SZ.v len /\ Seq.length d == SZ.v len /\
          SZ.v off + SZ.v len <= Seq.length contents /\
          SZ.fits (SZ.v off + SZ.v len) /\
          (forall (k:nat). k < SZ.v vj ==> Seq.index d k == Seq.index (Ghost.reveal contents) (SZ.v off + k)))
  decreases (SZ.v len - SZ.v (!j))
  {
    let vj = !j;
    FStar.SizeT.fits_lte (SZ.v off + SZ.v vj) (SZ.v off + SZ.v len);
    let src = Vec.op_Dot_Lparen_Rparen file (SZ.add off vj);
    dst.(vj) <- src;
    j := SZ.add vj 1sz;
  };
  ()
}

(* Fill the payload view for the scheduled event and establish the
   `local_pre_ok` obligation.  Only Server_send copies (block `cursor`, proved to
   be `hd pending`); Server_start/complete carry an empty payload. *)
fn fill_payload
  (cfg:tftp_server_config)
  (frame:tftp_server_endpoint_frame)
  (ev:TP.tftp_server_local)
  (lf:CC.tftp_server_local_frame)
  (st:Ghost.erased TP.tftp_server_state)
  (#cv:Ghost.erased (Seq.seq SZ.t))
  (#bv:Ghost.erased (Seq.seq U8.t))
  (#pc:Ghost.erased (Seq.seq U8.t))
requires
  Vec.pts_to frame.sef_cursor cv **
  Vec.pts_to cfg.scfg_file cfg.scfg_contents **
  pts_to lf.CC.tslf_buf pc **
  pure (Seq.length pc == SZ.v lf.CC.tslf_len /\ SZ.v lf.CC.tslf_len <= 512 /\
        scfg_wf cfg /\ cells_ok cv bv (Ghost.reveal st) /\
        server_plan_ok cfg (Ghost.reveal st) /\
        server_local_ready cfg ev lf (Ghost.reveal st))
ensures exists* (d:Seq.seq U8.t).
  Vec.pts_to frame.sef_cursor cv **
  Vec.pts_to cfg.scfg_file cfg.scfg_contents **
  pts_to lf.CC.tslf_buf d **
  pure (Seq.length d == SZ.v lf.CC.tslf_len /\
        CC.local_pre_ok ev (Ghost.reveal st) d lf.CC.tslf_blk lf.CC.tslf_len)
{
  match ev {
    TP.Server_send -> {
      let c = Vec.op_Dot_Lparen_Rparen frame.sef_cursor 0sz;
      let cn : Ghost.erased nat = Ghost.hide (SZ.v c);
      Plan.block_offset_le cfg.scfg_contents cfg.scfg_nblocks cn;
      Plan.block_slice cfg.scfg_contents cn;
      FStar.SizeT.fits_lte (SZ.v c * 512) (SZ.v cfg.scfg_nbytes_sz);
      let off = SZ.mul c 512sz;
      FStar.SizeT.fits_lte (SZ.v off + SZ.v lf.CC.tslf_len) (SZ.v cfg.scfg_nbytes_sz);
      copy_block cfg.scfg_file lf.CC.tslf_buf off lf.CC.tslf_len;
      with d1. _;
      (* d1 == block contents c == hd pending *)
      assert (pure (Seq.equal d1 (Plan.block cfg.scfg_contents cn)));
      Plan.blocks_of_unfold cfg.scfg_contents cn cfg.scfg_nblocks;
      Plan.blocks_of_plan_wf cfg.scfg_contents cn cfg.scfg_nblocks;
      assert (pure (Seq.equal (L.hd (Ghost.reveal st).TP.tss_pending) d1));
      ()
    }
    TP.Server_start filename plan -> {
      Plan.blocks_of_plan_wf cfg.scfg_contents 0 cfg.scfg_nblocks;
      ()
    }
    TP.Server_complete -> {
      Plan.blocks_of_empty cfg.scfg_contents cfg.scfg_nblocks cfg.scfg_nblocks;
      ()
    }
    TP.Server_abort -> { unreachable () }
    TP.Server_timeout -> { unreachable () }
  }
}

(* ───────────────────────────────────────────────────────────────────────────
   pe_prepare_local — fill the payload, lend the exact-length output view
   ─────────────────────────────────────────────────────────────────────────── *)

fn tftp_server_prepare_local
  (i:CC.tftp_server_impl)
  (cfg:tftp_server_config)
  (frame:tftp_server_endpoint_frame)
  (ch:TCP.channel)
  (ev:TP.tftp_server_local)
  (lf:CC.tftp_server_local_frame)
  (received:Ghost.erased TCP.bytes)
  (sent:Ghost.erased TCP.bytes)
  (st:Ghost.erased TP.tftp_server_state)
requires
  tftp_server_action_frame i cfg frame (Ghost.reveal st) (PE.EndpointLocal ev lf) **
  tftp_server_io_ready i ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st)
returns lio:tftp_server_endpoint_local_io
ensures
  tftp_server_local_io_continuation i ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) ev lio **
  PE.local_output_buffer
    (tftp_server_local_output lio)
    (tftp_server_local_output_len lio)
    (Ghost.reveal (tftp_server_local_old_output lio)) **
  CC.tftp_server_local_frame_pre
    ev lf (Ghost.reveal st)
    (tftp_server_local_output lio)
    (tftp_server_local_output_len lio)
    (Ghost.reveal (tftp_server_local_old_output lio)) **
  tftp_server_local_continuation i cfg frame (Ghost.reveal st) ev lf
{
  unfold (tftp_server_action_frame i cfg frame (Ghost.reveal st) (PE.EndpointLocal ev lf));
  with cv bv pc tsnfd. _;
  unfold (tftp_server_io_ready i ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  with raw outd ind. _;
  fill_payload cfg frame ev lf st #cv #bv;
  with d. _;
  (* the output view out[0..4+len) *)
  assert_norm (516 < pow2 16);
  FStar.SizeT.fits_lte (4 + SZ.v lf.CC.tslf_len) 516;
  let olen = SZ.add 4sz lf.CC.tslf_len;
  let ov = take_prefix frame.sef_out 516 olen;
  with opc. _;
  let lio : tftp_server_endpoint_local_io = {
    slo_output = ov;
    slo_output_len = olen;
    slo_old_output = Ghost.hide opc;
    slo_raw_received = Ghost.hide raw;
  };
  rewrite (TCP.is_channel ch raw (Ghost.reveal sent))
    as (TCP.is_channel ch (Ghost.reveal lio.slo_raw_received) (Ghost.reveal sent));
  rewrite (prefix_rest frame.sef_out 516 olen)
    as (prefix_rest frame.sef_out 516 lio.slo_output_len);
  fold (tftp_server_local_io_continuation i ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) ev lio);
  rewrite (pts_to ov opc)
    as (pts_to (tftp_server_local_output lio) (Ghost.reveal (tftp_server_local_old_output lio)));
  fold (PE.local_output_buffer
    (tftp_server_local_output lio)
    (tftp_server_local_output_len lio)
    (Ghost.reveal (tftp_server_local_old_output lio)));
  fold (CC.tftp_server_local_frame_pre
    ev lf (Ghost.reveal st)
    (tftp_server_local_output lio)
    (tftp_server_local_output_len lio)
    (Ghost.reveal (tftp_server_local_old_output lio)));
  fold (tftp_server_local_continuation i cfg frame (Ghost.reveal st) ev lf);
  lio
}

(* ───────────────────────────────────────────────────────────────────────────
   pe_finish_local_action — return the payload view, advance the cells,
   re-prove the coupling
   ─────────────────────────────────────────────────────────────────────────── *)

(* Server_send shifts the plan cursor by one while preserving the coupling. *)
let send_preserves_plan_ok
  (cfg:tftp_server_config) (st0 st1:TP.tftp_server_state)
  : Lemma
    (requires
      server_plan_ok cfg st0 /\
      Some? st0.TP.tss_filename /\ st0.TP.tss_status == FT.FT_InProgress /\
      L.length st0.TP.tss_sent < cfg.scfg_nblocks /\
      Cons? st0.TP.tss_pending /\ st1 == Log.send_next_state st0)
    (ensures
      server_plan_ok cfg st1 /\
      st1.TP.tss_filename == st0.TP.tss_filename /\
      L.length st1.TP.tss_sent == L.length st0.TP.tss_sent + 1)
  = Plan.lemma_send_shift cfg.scfg_contents (L.length st0.TP.tss_sent) cfg.scfg_nblocks;
    FStar.List.Tot.Properties.append_length st0.TP.tss_sent [L.hd st0.TP.tss_pending]

(* Server_start establishes the coupling from the initial state. *)
let start_preserves_plan_ok
  (cfg:tftp_server_config) (st1:TP.tftp_server_state)
  (filename:TCP.bytes) (plan:list TCP.bytes)
  : Lemma
    (requires
      filename == Ghost.reveal cfg.scfg_filename /\ plan == Ghost.reveal (plan_of cfg) /\
      st1 == Log.start_next_state filename plan)
    (ensures
      server_plan_ok cfg st1 /\ Some? st1.TP.tss_filename /\
      L.length st1.TP.tss_sent == 0)
  = Plan.blocks_of_empty cfg.scfg_contents 0 0

(* Server_complete flips status to Completed: the coupling becomes vacuous. *)
let complete_preserves_plan_ok
  (cfg:tftp_server_config) (st0 st1:TP.tftp_server_state)
  : Lemma
    (requires
      server_plan_ok cfg st0 /\ Some? st0.TP.tss_filename /\
      st1 == Log.complete_next_state st0)
    (ensures
      server_plan_ok cfg st1 /\ st1.TP.tss_filename == st0.TP.tss_filename /\
      L.length st1.TP.tss_sent == L.length st0.TP.tss_sent)
  = ()

fn tftp_server_finish_local_action
  (i:CC.tftp_server_impl)
  (cfg:tftp_server_config)
  (frame:tftp_server_endpoint_frame)
  (ev:TP.tftp_server_local)
  (lf:CC.tftp_server_local_frame)
  (result:CPI.process_result)
  (old_out:Ghost.erased TCP.bytes)
  (out_contents:Ghost.erased TCP.bytes)
  (st0:Ghost.erased TP.tftp_server_state)
  (st1:Ghost.erased TP.tftp_server_state)
  (wire_outputs:Ghost.erased (list tftp_message))
  (local_outputs:Ghost.erased (list unit))
requires
  tftp_server_local_continuation i cfg frame (Ghost.reveal st0) ev lf **
  CC.tftp_server_local_frame_post
    ev lf result (Ghost.reveal old_out) (Ghost.reveal out_contents)
    (Ghost.reveal st0) (Ghost.reveal st1)
    (Ghost.reveal wire_outputs) (Ghost.reveal local_outputs)
ensures tftp_server_frame_ready i cfg frame (Ghost.reveal st1)
{
  unfold (tftp_server_local_continuation i cfg frame (Ghost.reveal st0) ev lf);
  with cv bv tsnfd. _;
  unfold (CC.tftp_server_local_frame_post
    ev lf result (Ghost.reveal old_out) (Ghost.reveal out_contents)
    (Ghost.reveal st0) (Ghost.reveal st1)
    (Ghost.reveal wire_outputs) (Ghost.reveal local_outputs));
  with d. _;
  give_back_prefix frame.sef_blk 512 lf.CC.tslf_len lf.CC.tslf_buf;
  match ev {
    TP.Server_send -> {
      let c = Vec.op_Dot_Lparen_Rparen frame.sef_cursor 0sz;
      FStar.SizeT.fits_lte (SZ.v c + 1) (SZ.v cfg.scfg_nblocks_sz);
      Vec.op_Dot_Lparen_Rparen_Less_Minus frame.sef_cursor 0sz (SZ.add c 1sz);
      send_preserves_plan_ok cfg (Ghost.reveal st0) (Ghost.reveal st1);
      fold (tftp_server_frame_ready i cfg frame (Ghost.reveal st1))
    }
    TP.Server_start filename plan -> {
      Vec.op_Dot_Lparen_Rparen_Less_Minus frame.sef_cursor 0sz 0sz;
      Vec.op_Dot_Lparen_Rparen_Less_Minus frame.sef_started 0sz 1uy;
      start_preserves_plan_ok cfg (Ghost.reveal st1) filename plan;
      fold (tftp_server_frame_ready i cfg frame (Ghost.reveal st1))
    }
    TP.Server_complete -> {
      complete_preserves_plan_ok cfg (Ghost.reveal st0) (Ghost.reveal st1);
      fold (tftp_server_frame_ready i cfg frame (Ghost.reveal st1))
    }
    TP.Server_abort -> { unreachable () }
    TP.Server_timeout -> { unreachable () }
  }
}

(* ───────────────────────────────────────────────────────────────────────────
   pe_finish_local_io — write produced bytes, return the output view,
   re-establish io_ready
   ─────────────────────────────────────────────────────────────────────────── *)

fn tftp_server_finish_local_io
  (i:CC.tftp_server_impl)
  (ch:TCP.channel)
  (frame:tftp_server_endpoint_frame)
  (lio:tftp_server_endpoint_local_io)
  (ev:TP.tftp_server_local)
  (result:CPI.process_result)
  (received0:Ghost.erased TCP.bytes)
  (sent0:Ghost.erased TCP.bytes)
  (st0:Ghost.erased TP.tftp_server_state)
  (received1:Ghost.erased TCP.bytes)
  (sent1:Ghost.erased TCP.bytes)
  (st1:Ghost.erased TP.tftp_server_state)
  (out_contents:Ghost.erased TCP.bytes)
  (wire_outputs:Ghost.erased (list tftp_message))
  (local_outputs:Ghost.erased (list unit))
requires
  tftp_server_local_io_continuation i ch frame (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) ev lio **
  pts_to (tftp_server_local_output lio) (Ghost.reveal out_contents) **
  pure (
    CPI.local_process_correct
      (CC.tftp_server_protocol_implementation.CPI.pi_system i)
      ev
      (Ghost.reveal (tftp_server_local_old_output lio))
      (Ghost.reveal out_contents)
      (tftp_server_local_output_len lio)
      (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0)
      result
      (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1)
      (Ghost.reveal wire_outputs) (Ghost.reveal local_outputs))
ensures tftp_server_io_ready i ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1)
{
  unfold (tftp_server_local_io_continuation i ch frame (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) ev lio);
  with ind. _;
  CPI.lemma_local_process_sent_output_prefix
    (CC.tftp_server_protocol_implementation.CPI.pi_system i)
    ev
    (Ghost.reveal (tftp_server_local_old_output lio))
    (Ghost.reveal out_contents)
    (tftp_server_local_output_len lio)
    (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0)
    result
    (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1)
    (Ghost.reveal wire_outputs) (Ghost.reveal local_outputs);
  assert (pure (SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)));
  let nwritten = TCP.write ch (tftp_server_local_output lio) result.CPI.process_produced_len;
  assert (pure (nwritten == result.CPI.process_produced_len));
  rewrite
    (TCP.is_channel ch (Ghost.reveal lio.slo_raw_received)
      (Seq.append (Ghost.reveal sent0)
        (if SZ.v nwritten <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v nwritten)
         else Seq.create 0 0uy)))
    as
    (TCP.is_channel ch (Ghost.reveal lio.slo_raw_received)
      (Seq.append (Ghost.reveal sent0)
        (if SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v result.CPI.process_produced_len)
         else Seq.create 0 0uy)));
  assert (pure (Seq.equal (Ghost.reveal sent1)
    (Seq.append (Ghost.reveal sent0)
      (CPI.output_prefix (Ghost.reveal out_contents) result.CPI.process_produced_len))));
  rewrite
    (TCP.is_channel ch (Ghost.reveal lio.slo_raw_received)
      (Seq.append (Ghost.reveal sent0)
        (if SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v result.CPI.process_produced_len)
         else Seq.create 0 0uy)))
    as
    (TCP.is_channel ch (Ghost.reveal lio.slo_raw_received) (Ghost.reveal sent1));
  rewrite (pts_to (tftp_server_local_output lio) (Ghost.reveal out_contents))
    as (pts_to lio.slo_output (Ghost.reveal out_contents));
  pts_to_len lio.slo_output;
  give_back_prefix frame.sef_out 516 lio.slo_output_len lio.slo_output;
  fold (tftp_server_io_ready i ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1))
}

(* ───────────────────────────────────────────────────────────────────────────
   The 28-field endpoint instance
   ─────────────────────────────────────────────────────────────────────────── *)

let tftp_server_protocol_endpoint
  : PE.protocol_endpoint
      CC.tftp_server_impl
      TP.tftp_server_state
      tftp_message
      TP.tftp_server_local
      unit
      CC.tftp_server_protocol_implementation
  =
  {
    PE.pe_config = tftp_server_config;
    PE.pe_frame = tftp_server_endpoint_frame;
    PE.pe_frame_ready = tftp_server_frame_ready;
    PE.pe_io_ready = tftp_server_io_ready;
    PE.pe_action_frame = tftp_server_action_frame;
    PE.pe_network_continuation = tftp_server_network_continuation;
    PE.pe_local_continuation = tftp_server_local_continuation;
    PE.pe_next_action = tftp_server_next_action;
    PE.pe_cancel_action = tftp_server_cancel_action;
    PE.pe_finish_network_action = tftp_server_finish_network_action;
    PE.pe_finish_local_action = tftp_server_finish_local_action;
    PE.pe_network_io = tftp_server_endpoint_network_io;
    PE.pe_network_io_continuation = tftp_server_network_io_continuation;
    PE.pe_network_input = tftp_server_network_input;
    PE.pe_network_input_len = tftp_server_network_input_len;
    PE.pe_network_output = tftp_server_network_output;
    PE.pe_network_output_len = tftp_server_network_output_len;
    PE.pe_network_input_contents = tftp_server_network_input_contents;
    PE.pe_network_old_output = tftp_server_network_old_output;
    PE.pe_prepare_network = tftp_server_prepare_network;
    PE.pe_finish_network_io = tftp_server_finish_network_io;
    PE.pe_local_io = tftp_server_endpoint_local_io;
    PE.pe_local_io_continuation = tftp_server_local_io_continuation;
    PE.pe_local_output = tftp_server_local_output;
    PE.pe_local_output_len = tftp_server_local_output_len;
    PE.pe_local_old_output = tftp_server_local_old_output;
    PE.pe_prepare_local = tftp_server_prepare_local;
    PE.pe_finish_local_io = tftp_server_finish_local_io;
  }
