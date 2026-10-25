module TLS13.Impl.X509.Cert

(** Verified certificate parsing and per-certificate path checks, as a
    transcription of [TLS13.X509.Spec.parse_certificate],
    [path_certificate_ok], [leaf_ok] and [issuer_ok]. *)

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
open TLS13.Impl.X509.Fields

module A = Pulse.Lib.Array
module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module N = TLS13.Impl.X509.Names
module PK = TLS13.Impl.X509.PublicKey
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module X = TLS13.X509.Spec

inline_for_extraction noextract unfold let ( +^ ) = SZ.add
inline_for_extraction noextract unfold let ( -^ ) = SZ.sub

(** {2 TBSCertificate} *)

let ver_spec (c:B.bytes) (ts te:nat) : option (nat & nat) =
  match C.der_tlv c 0xA0uy ts te with
  | Some (vs, ve) ->
    (match C.der_tlv c 0x02uy vs ve with
     | Some (is, ie) ->
       if ie = ve && ie = is + 1 && (Seq.index c is = 1uy || Seq.index c is = 2uy)
       then Some (U8.v (Seq.index c is) + 1, ve)
       else None
     | None -> None)
  | None -> Some (1, ts)

type ver_v = {
  v_ok: bool;
  v_ver: U8.t;
  v_end: SZ.t;
}

let ver_matches (r:ver_v) (o:option (nat & nat)) : prop =
  match o with
  | Some (v, e) -> r.v_ok == true /\ U8.v r.v_ver == v /\ SZ.v r.v_end == e
  | None -> r.v_ok == false

fn parse_version
  (c:array U8.t) (len:SZ.t) (ts te:SZ.t)
  requires pts_to c 'b ** pure (ok_len 'b len)
  returns r:ver_v
  ensures pts_to c 'b ** pure (ver_matches r (ver_spec (cb 'b len) (SZ.v ts) (SZ.v te)))
{
  let v = PK.der_tlv_impl c len 0xA0uy ts te;
  if (v.ok) {
    let i = PK.der_tlv_impl c len 0x02uy v.lo v.hi;
    if (i.ok && i.hi = v.hi && i.hi = i.lo +^ 1sz) {
      let x = c.(i.lo);
      if (x = 1uy || x = 2uy) {
        ({ v_ok = true; v_ver = U8.add x 1uy; v_end = v.hi })
      } else {
        ({ v_ok = false; v_ver = 0uy; v_end = 0sz })
      }
    } else {
      ({ v_ok = false; v_ver = 0uy; v_end = 0sz })
    }
  } else {
    ({ v_ok = true; v_ver = 1uy; v_end = ts })
  }
}

let exts_spec (c:B.bytes) (version:nat) (p te:nat) : option (nat & nat) =
  if p = te then Some (te, te)
  else
    match C.der_tlv c 0xA3uy p te with
    | Some (xs, xe) ->
      if xe <> te || version <> 3 then None
      else
        (match C.der_tlv c 0x30uy xs xe with
         | Some (ls, le) ->
           if le <> xe || not (X.extensions_wf c ls le) then None else Some (ls, le)
         | None -> None)
    | None -> None

#push-options "--z3rlimit 40"
fn parse_exts
  (c:array U8.t) (len:SZ.t) (version:U8.t) (p te:SZ.t)
  requires pts_to c 'b ** pure (ok_len 'b len /\ SZ.v te <= SZ.v len)
  returns r:PK.der_range
  ensures pts_to c 'b **
          pure (opt_range_matches r (exts_spec (cb 'b len) (U8.v version) (SZ.v p) (SZ.v te)) /\
                (r.ok ==> SZ.v r.lo <= SZ.v r.hi /\ SZ.v r.hi <= SZ.v te))
{
  if (p = te) {
    ({ PK.ok = true; PK.lo = te; PK.hi = te })
  } else {
    let x = PK.der_tlv_impl c len 0xA3uy p te;
    if (x.ok && x.hi = te && version = 3uy) {
      let l = PK.der_tlv_impl c len 0x30uy x.lo x.hi;
      if (l.ok && l.hi = x.hi) {
        let wf = extensions_wf c len l.lo l.hi;
        if (wf) { l } else { PK.no_range }
      } else {
        PK.no_range
      }
    } else {
      PK.no_range
    }
  }
}
#pop-options

let parse_tbs_alt (c:B.bytes) (ts te:nat) : option X.tbs_fields =
           (match ver_spec c ts te with
            | None -> None
            | Some (version, p) ->
            match C.der_tlv c 0x02uy p te with
            | None -> None
            | Some (_, serial_end) ->
            match C.der_tlv c 0x30uy serial_end te with
            | None -> None
            | Some (a_s, a_e) ->
            match C.der_tlv c 0x30uy a_e te with
            | None -> None
            | Some (_, issuer_end) ->
            match C.der_tlv c 0x30uy issuer_end te with
            | None -> None
            | Some (vs, ve) ->
            match X.parse_time c vs ve with
            | None -> None
            | Some (not_before, p1) ->
            match X.parse_time c p1 ve with
            | None -> None
            | Some (not_after, p2) ->
            if p2 <> ve then None else
            match C.der_tlv c 0x30uy ve te with
            | None -> None
            | Some (_, subject_end) ->
            match C.der_tlv c 0x30uy subject_end te with
            | None -> None
            | Some (_, spki_end) ->
            let p : nat = match C.der_tlv c 0x81uy spki_end te with Some r -> snd r | None -> spki_end in
            let p : nat = match C.der_tlv c 0x82uy p te with Some r -> snd r | None -> p in
            match exts_spec c version p te with
            | None -> None
            | Some (ext_s, ext_e) ->
              Some {
                X.version; X.alg_s = a_s; X.alg_e = a_e; X.issuer_s = a_e;
                X.issuer_e = issuer_end; X.not_before; X.not_after;
                X.subject_s = ve; X.subject_e = subject_end; X.ext_s; X.ext_e })

let parse_tbs_eq (c:B.bytes) (ts te:nat)
  : Lemma (X.parse_tbs c ts te == parse_tbs_alt c ts te)
  = assert (X.parse_tbs c ts te == parse_tbs_alt c ts te)
      by (FStar.Tactics.V2.norm [delta_only [`%X.parse_tbs; `%parse_tbs_alt; `%ver_spec; `%exts_spec];
                                 zeta; iota];
          FStar.Tactics.V2.trefl ())

type pcert = {
  pc_ok: bool;
  tbs_s: SZ.t;
  tbs_e: SZ.t;
  sig_alg_s: SZ.t;
  sig_alg_e: SZ.t;
  sig_s: SZ.t;
  sig_e: SZ.t;
  version: U8.t;
  alg_s: SZ.t;
  alg_e: SZ.t;
  issuer_s: SZ.t;
  issuer_e: SZ.t;
  not_before: U64.t;
  not_after: U64.t;
  subject_s: SZ.t;
  subject_e: SZ.t;
  ext_s: SZ.t;
  ext_e: SZ.t;
}

inline_for_extraction noextract
let no_pcert : pcert = {
  pc_ok = false; tbs_s = 0sz; tbs_e = 0sz; sig_alg_s = 0sz; sig_alg_e = 0sz;
  sig_s = 0sz; sig_e = 0sz; version = 0uy; alg_s = 0sz; alg_e = 0sz;
  issuer_s = 0sz; issuer_e = 0sz; not_before = 0UL; not_after = 0UL;
  subject_s = 0sz; subject_e = 0sz; ext_s = 0sz; ext_e = 0sz }

let to_fields (r:pcert) : X.tbs_fields = {
  X.version = U8.v r.version;
  X.alg_s = SZ.v r.alg_s; X.alg_e = SZ.v r.alg_e;
  X.issuer_s = SZ.v r.issuer_s; X.issuer_e = SZ.v r.issuer_e;
  X.not_before = U64.v r.not_before; X.not_after = U64.v r.not_after;
  X.subject_s = SZ.v r.subject_s; X.subject_e = SZ.v r.subject_e;
  X.ext_s = SZ.v r.ext_s; X.ext_e = SZ.v r.ext_e }

let to_pc (r:pcert) : X.parsed_certificate = {
  X.tbs_s = SZ.v r.tbs_s; X.tbs_e = SZ.v r.tbs_e; X.fields = to_fields r;
  X.sig_alg_s = SZ.v r.sig_alg_s; X.sig_alg_e = SZ.v r.sig_alg_e;
  X.sig_s = SZ.v r.sig_s; X.sig_e = SZ.v r.sig_e }

(** Every range of [r] lies within [c[0, n)]. *)
let pcert_bounded (r:pcert) (n:nat) : prop =
  SZ.v r.tbs_s <= SZ.v r.tbs_e /\ SZ.v r.tbs_e <= n /\
  SZ.v r.sig_alg_s <= SZ.v r.sig_alg_e /\ SZ.v r.sig_alg_e <= n /\
  SZ.v r.sig_s <= SZ.v r.sig_e /\ SZ.v r.sig_e <= n /\
  SZ.v r.alg_s <= SZ.v r.alg_e /\ SZ.v r.alg_e <= n /\
  SZ.v r.issuer_s <= SZ.v r.issuer_e /\ SZ.v r.issuer_e <= n /\
  SZ.v r.subject_s <= SZ.v r.subject_e /\ SZ.v r.subject_e <= n /\
  SZ.v r.ext_s <= SZ.v r.ext_e /\ SZ.v r.ext_e <= n

(** [r] is the TBS part of [parse_tbs c ts te]; the outer fields are
    unconstrained. *)
let tbs_matches (r:pcert) (c:B.bytes) (ts te:nat) : prop =
  match X.parse_tbs c ts te with
  | Some f ->
    r.pc_ok == true /\ to_fields r == f /\
    SZ.v r.alg_s <= SZ.v r.alg_e /\ SZ.v r.alg_e <= te /\
    SZ.v r.issuer_s <= SZ.v r.issuer_e /\ SZ.v r.issuer_e <= te /\
    SZ.v r.subject_s <= SZ.v r.subject_e /\ SZ.v r.subject_e <= te /\
    SZ.v r.ext_s <= SZ.v r.ext_e /\ SZ.v r.ext_e <= te /\ te <= B.length c
  | None -> r.pc_ok == false

#push-options "--z3rlimit 200 --fuel 0 --ifuel 1"
fn parse_tbs
  (c:array U8.t) (len:SZ.t) (ts te:SZ.t)
  requires pts_to c 'b ** pure (ok_len 'b len)
  returns r:pcert
  ensures pts_to c 'b ** pure (tbs_matches r (cb 'b len) (SZ.v ts) (SZ.v te))
{
  parse_tbs_eq (cb 'b len) (SZ.v ts) (SZ.v te);
  let ver = parse_version c len ts te;
  if (not ver.v_ok) { no_pcert } else {
  let serial = PK.der_tlv_impl c len 0x02uy ver.v_end te;
  if (not serial.ok) { no_pcert } else {
  let alg = PK.der_tlv_impl c len 0x30uy serial.hi te;
  if (not alg.ok) { no_pcert } else {
  let iss = PK.der_tlv_impl c len 0x30uy alg.hi te;
  if (not iss.ok) { no_pcert } else {
  let vld = PK.der_tlv_impl c len 0x30uy iss.hi te;
  if (not vld.ok) { no_pcert } else {
  let nb = parse_time c len vld.lo vld.hi;
  if (not nb.tr_ok) { no_pcert } else {
  let na = parse_time c len nb.tr_end vld.hi;
  if (not na.tr_ok || na.tr_end <> vld.hi) { no_pcert } else {
  let subj = PK.der_tlv_impl c len 0x30uy vld.hi te;
  if (not subj.ok) { no_pcert } else {
  let spki = PK.der_tlv_impl c len 0x30uy subj.hi te;
  if (not spki.ok) { no_pcert } else {
  let u1 = PK.der_tlv_impl c len 0x81uy spki.hi te;
  let p1 = (if u1.ok then u1.hi else spki.hi);
  let u2 = PK.der_tlv_impl c len 0x82uy p1 te;
  let p2 = (if u2.ok then u2.hi else p1);
  let x = parse_exts c len ver.v_ver p2 te;
  if (not x.ok) { no_pcert } else {
  ({ no_pcert with
     pc_ok = true; version = ver.v_ver; alg_s = alg.lo; alg_e = alg.hi;
     issuer_s = alg.hi; issuer_e = iss.hi; not_before = nb.tr_val; not_after = na.tr_val;
     subject_s = vld.hi; subject_e = subj.hi; ext_s = x.lo; ext_e = x.hi })
  }}}}}}}}}}
}
#pop-options

let pcert_matches (r:pcert) (c:B.bytes) : prop =
  match X.parse_certificate c with
  | Some pc -> r.pc_ok == true /\ to_pc r == pc /\ pcert_bounded r (B.length c)
  | None -> r.pc_ok == false

#push-options "--z3rlimit 100"
fn parse_certificate
  (c:array U8.t) (len:SZ.t)
  requires pts_to c 'b ** pure (ok_len 'b len)
  returns r:pcert
  ensures pts_to c 'b ** pure (pcert_matches r (cb 'b len))
{
  let cs = PK.der_tlv_impl c len 0x30uy 0sz len;
  if (not cs.ok || cs.hi <> len) { no_pcert } else {
  let ts = PK.der_tlv_impl c len 0x30uy cs.lo cs.hi;
  if (not ts.ok) { no_pcert } else {
  let al = PK.der_tlv_impl c len 0x30uy ts.hi cs.hi;
  if (not al.ok) { no_pcert } else {
  let bs = PK.der_tlv_impl c len 0x03uy al.hi cs.hi;
  if (not bs.ok || bs.hi <> cs.hi || SZ.gte bs.lo bs.hi) { no_pcert } else {
  let z = c.(bs.lo);
  if (z <> 0x00uy) { no_pcert } else {
  let t = parse_tbs c len ts.lo ts.hi;
  if (not t.pc_ok) { no_pcert } else {
  ({ t with tbs_s = cs.lo; tbs_e = ts.hi; sig_alg_s = al.lo; sig_alg_e = al.hi;
            sig_s = bs.lo +^ 1sz; sig_e = bs.hi })
  }}}}}}
}
#pop-options

(** {2 Path checks} *)

let pc_ok (r:pcert) (c:B.bytes) : prop =
  r.pc_ok == true /\ X.parse_certificate c == Some (to_pc r) /\ pcert_bounded r (B.length c)

(** Validation times at or past 2^40 seconds are rejected. *)
let max_time : (r:U64.t{U64.v r == 0x10000000000}) = 0x10000000000UL

let epoch_seconds64 : (r:U64.t{U64.v r == X.epoch_seconds}) = 62135596800UL

inline_for_extraction
let add_epoch (t:U64.t{U64.v t < 0x10000000000})
  : r:U64.t{U64.v r == U64.v t + X.epoch_seconds}
  = U64.add t epoch_seconds64

#push-options "--z3rlimit 60"
fn path_certificate_ok
  (c:array U8.t) (len:SZ.t) (r:pcert) (t:U64.t)
  requires pts_to c 'b ** pure (ok_len 'b len /\ pc_ok r (cb 'b len))
  returns ok:bool
  ensures pts_to c 'b **
          pure (ok ==> X.path_certificate_ok (cb 'b len) (to_pc r) (U64.v t))
{
  if (U64.gte t max_time) {
    false
  } else {
    let now = add_epoch t;
    let same = range_eq_self c len r.sig_alg_s r.sig_alg_e r.alg_s r.alg_e;
    let x = extensions_ok c len r.ext_s r.ext_e;
    let k = ext_key_usage_ok c len r.ext_s r.ext_e;
    (r.version = 3uy && same && U64.lte r.not_before now && U64.lte now r.not_after && x && k)
  }
}
#pop-options

fn leaf_ok
  (c:array U8.t) (len:SZ.t) (r:pcert)
  (h:array U8.t) (hlen:SZ.t)
  requires pts_to c 'b ** pts_to h 'hb **
           pure (ok_len 'b len /\ ok_len 'hb hlen /\ pc_ok r (cb 'b len))
  returns ok:bool
  ensures pts_to c 'b ** pts_to h 'hb **
          pure (ok == X.leaf_ok (cb 'b len) (to_pc r) (cb 'hb hlen))
{
  let s = N.subject_alt_name_ok c len r.ext_s r.ext_e h hlen;
  let k = key_usage_allows c len r.ext_s r.ext_e 0x80uy;
  (s && k)
}

fn issuer_ok
  (c:array U8.t) (len:SZ.t) (r:pcert) (below:SZ.t)
  requires pts_to c 'b ** pure (ok_len 'b len /\ pc_ok r (cb 'b len))
  returns ok:bool
  ensures pts_to c 'b ** pure (ok == X.issuer_ok (cb 'b len) (to_pc r) (SZ.v below))
{
  let f = find_extension c len r.ext_s r.ext_e X.oid_basic_constraints;
  let k = key_usage_allows c len r.ext_s r.ext_e 0x04uy;
  if (f.ok) {
    let a = ca_allows c len f.lo f.hi below;
    (a && k)
  } else {
    false
  }
}
