module TLS13.Security.Game

(**
  Stage 2: the multi-session key-indistinguishability game for the TLS 1.3
  1-RTT (EC)DHE handshake with server authentication, and its ideal-world
  security theorem.  See SECURITY_DESIGN_AND_IMPL.md for the overall argument.

  The game is parametric in a key oracle [o] (secrets by public index, see
  [TLS13.Security.Oracle]) and in the answer [a] the Test query returns.

  * Honest sessions draw their ephemeral (EC)DH keys from game coins: session
    number [n] uses [coins n].
  * Server signatures are ideal: an honest server logs what it signs, and a
    client accepts a CertificateVerify for an uncorrupted identity only if
    that content was logged.  For a corrupted identity the client accepts
    any CertificateVerify (the adversary can sign anything).  The signed
    content is the exchange and the transcript up to the CertificateVerify;
    the real TLS signature covers the transcript hash, which contains both
    key shares, so this abstraction is hops H3 (collision resistance) and H5
    (EUF-CMA) of the design document.
  * Finished MACs are computed with finished keys obtained from the oracle.
  * Handshake record encryption is not modeled: the adversary sees and
    injects handshake plaintexts, and may reveal the handshake record keys
    (AEAD key and IV) of any session, from which a reduction simulates the
    encrypted record layer (multi-stage key-exchange style).  Handshake
    traffic SECRETS are never revealed: the finished keys are derived from
    them, so revealing them would invalidate the PRF hop that makes finished
    keys and record keys independent.
  * Application traffic secrets may be revealed, except at the tested
    index.
  * The adversary is an arbitrary deterministic function of its view.

  In the ideal world ([ideal_oracle]) every index whose exchange is honest --
  both shares come from game coins -- is answered from a random tape.  The
  main theorem [theorem_key_indistinguishability] states that the real-key
  and random-key worlds produce identical views, under a resampling of the
  tape at the test index: since tape entries are independent and uniform,
  the two worlds are equally distributed.  The tape-resampling step and the
  real-to-ideal oracle hops are the paper arguments listed in the design
  document.
**)

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module L = FStar.List.Tot
module Tr = TLS13.Transcript

open TLS13.Spec.StateMachine
open TLS13.Security.Index
open TLS13.Security.Oracle

(** {1 Game data} *)

type ident = nat

(** Ephemeral (EC)DH keys of the honest sessions, by session number. *)
type coins = nat -> C.kex_private

let share (cs:coins) (g:C.dh_group) (n:nat) : GTot B.bytes =
  C.kex_public_from_private g (cs n)

(** What an honest server signs in its CertificateVerify. *)
type sig_content = {
  sig_kex: kex_index;
  sig_transcript: B.bytes;
}

type client_phase =
  | CWaitServerHello of B.bytes                         (* ClientHello bytes *)
  | CWaitFlight of kex_index & B.bytes                  (* exchange, CH..SH *)
  | CAccepted of kex_index & B.bytes & B.bytes & bool   (* .., CH..SF, authenticated *)
  | CFailed

type server_phase =
  | SWaitFinished of kex_index & B.bytes & B.bytes      (* exchange, CH..SH, CH..SF *)
  | SAccepted of kex_index & B.bytes & B.bytes
  | SFailed

type session =
  | ClientSession of C.dh_group & ident & client_phase  (* group, intended server *)
  | ServerSession of C.dh_group & ident & server_phase  (* group, own identity *)

(** Oracle queries made by the game, recorded so that the run can be shown to
    depend on the oracle only at these points. *)
type logged =
  | LKey of secret_index
  | LTest of traffic_index

type game_state = {
  sessions: list session;          (* session number = position *)
  corrupted: list ident;
  sig_log: list (ident & sig_content);
  revealed: list traffic_index;
  tested: option traffic_index;
  log: list logged;
}

let initial_state : game_state = {
  sessions = [];
  corrupted = [];
  sig_log = [];
  revealed = [];
  tested = None;
  log = [];
}

type query =
  | QStartClient of C.dh_group & ident & B.bytes
    (* group, intended server, ClientHello bytes *)
  | QServerHello of nat & B.bytes & B.bytes
    (* client session, server share, ServerHello bytes *)
  | QStartServer of C.dh_group & ident & B.bytes & B.bytes & B.bytes & B.bytes & B.bytes
    (* group, identity, client share, CH bytes, SH bytes, EE..Cert bytes, CV bytes *)
  | QServerFlight of nat & B.bytes & B.bytes & B.bytes
    (* client session, EE..Cert bytes, CV bytes, server Finished *)
  | QClientFinished of nat & B.bytes
    (* server session, client Finished *)
  | QCorrupt of ident
  | QRevealRecordKeys of nat & traffic_label & C.aead_alg
    (* handshake record key and IV of a session, for an AEAD algorithm *)
  | QReveal of nat & traffic_label
    (* application traffic secret of a session *)
  | QTest of nat & traffic_label

type response =
  | ROk
  | RFail
  | RShare of B.bytes
  | RServerFlight of B.bytes & B.bytes   (* server share, server Finished *)
  | RClientFinished of B.bytes
  | RAccept of bool
  | RKey of option B.bytes
  | RRecordKeys of option B.bytes & option B.bytes

type adversary = list response -> query

(** The value Test returns, by test index. *)
type answer_oracle = traffic_index -> GTot (option B.bytes)

(** {1 Helpers} *)

let rec update_nth (#a:Type) (l:list a) (n:nat) (x:a) : Tot (list a) (decreases l) =
  match l with
  | [] -> []
  | h :: t -> if n = 0 then x :: t else h :: update_nth t (n - 1) x

let rec lemma_update_nth_length (#a:Type) (l:list a) (n:nat) (x:a)
  : Lemma (L.length (update_nth l n x) == L.length l)
          [SMTPat (L.length (update_nth l n x))]
= match l with
  | [] -> ()
  | _ :: t -> if n = 0 then () else lemma_update_nth_length t (n - 1) x

let rec lemma_update_nth_index (#a:Type) (l:list a) (n:nat) (x:a) (i:nat{i < L.length l})
  : Lemma (L.index (update_nth l n x) i == (if i = n then x else L.index l i))
          (decreases l)
= match l with
  | _ :: t -> if i = 0 || n = 0 then () else lemma_update_nth_index t (n - 1) x (i - 1)

let rec lemma_snoc_index (#a:Type) (l:list a) (x:a) (i:nat{i <= L.length l})
  : Lemma (L.length (L.append l [x]) == L.length l + 1 /\
           L.index (L.append l [x]) i == (if i = L.length l then x else L.index l i))
          (decreases l)
= L.append_length l [x];
  match l with
  | [] -> ()
  | _ :: t -> if i = 0 then () else lemma_snoc_index t x (i - 1)

let session_at (st:game_state) (s:nat) : option session =
  if s < L.length st.sessions then Some (L.index st.sessions s) else None

let set_session (st:game_state) (s:nat) (x:session) : game_state =
  { st with sessions = update_nth st.sessions s x }

let add_session (st:game_state) (x:session) : game_state =
  { st with sessions = L.append st.sessions [x] }

let hs_index (k:kex_index) (label:traffic_label) (th_sh:B.bytes) : traffic_index =
  { ti_kex = k; ti_epoch = TrafficHandshake; ti_label = label; ti_transcript = th_sh }

let app_index (k:kex_index) (label:traffic_label) (th_sf:B.bytes) : traffic_index =
  { ti_kex = k; ti_epoch = TrafficApplication; ti_label = label; ti_transcript = th_sf }

(** A Finished MAC: HMAC under the finished key of the transcript hash. *)
let mac (fk:B.bytes) (th:B.bytes) : GTot B.bytes =
  C.hmac_sha256 fk (Tr.hash th)

(** The traffic index a session holds for an epoch and direction. *)
let session_traffic_index (x:session) (epoch:traffic_epoch) (label:traffic_label)
  : option traffic_index =
  match x, epoch with
  | ClientSession (_, _, CWaitFlight (k, th_sh)), TrafficHandshake
  | ClientSession (_, _, CAccepted (k, th_sh, _, _)), TrafficHandshake
  | ServerSession (_, _, SWaitFinished (k, th_sh, _)), TrafficHandshake
  | ServerSession (_, _, SAccepted (k, th_sh, _)), TrafficHandshake ->
    Some (hs_index k label th_sh)
  | ClientSession (_, _, CAccepted (k, _, th_sf, _)), TrafficApplication
  | ServerSession (_, _, SWaitFinished (k, _, th_sf)), TrafficApplication
  | ServerSession (_, _, SAccepted (k, _, th_sf)), TrafficApplication ->
    Some (app_index k label th_sf)
  | _, _ -> None

(** {1 The game} *)

let step_server_hello (cs:coins) (st:game_state) (s:nat) (server_share sh:B.bytes)
  : GTot (game_state & response) =
  match session_at st s with
  | Some (ClientSession (g, peer, CWaitServerHello ch)) ->
    let k = { kx_group = g; kx_client_share = share cs g s; kx_server_share = server_share } in
    (set_session st s (ClientSession (g, peer, CWaitFlight (k, B.append ch sh))), ROk)
  | _ -> (st, RFail)

let step_start_server
  (cs:coins) (o:key_oracle) (st:game_state)
  (g:C.dh_group) (id:ident) (client_share ch sh ee_cert cv:B.bytes)
  : GTot (game_state & response) =
  let n = L.length st.sessions in
  let k = { kx_group = g; kx_client_share = client_share; kx_server_share = share cs g n } in
  let th_sh = B.append ch sh in
  let th_cv = B.append th_sh ee_cert in
  let th_pre = B.append th_cv cv in
  let i = IdxFinishedKey (hs_index k ServerTraffic th_sh) in
  let st1 = { st with log = LKey i :: st.log } in
  match o i with
  | Some fk ->
    let sf = mac fk th_pre in
    let st2 = { st1 with sig_log = (id, { sig_kex = k; sig_transcript = th_cv }) :: st1.sig_log } in
    (add_session st2 (ServerSession (g, id, SWaitFinished (k, th_sh, B.append th_pre sf))),
     RServerFlight (share cs g n, sf))
  | None ->
    (add_session st1 (ServerSession (g, id, SFailed)), RFail)

let step_server_flight
  (o:key_oracle) (st:game_state) (s:nat) (ee_cert cv sf:B.bytes)
  : GTot (game_state & response) =
  match session_at st s with
  | Some (ClientSession (g, peer, CWaitFlight (k, th_sh))) ->
    let th_cv = B.append th_sh ee_cert in
    let corrupt = L.mem peer st.corrupted in
    let sig_ok = corrupt || L.mem (peer, { sig_kex = k; sig_transcript = th_cv }) st.sig_log in
    let i = IdxFinishedKey (hs_index k ServerTraffic th_sh) in
    let st1 = { st with log = LKey i :: st.log } in
    let failed = set_session st1 s (ClientSession (g, peer, CFailed)) in
    (match o i with
     | Some fk ->
       let th_pre = B.append th_cv cv in
       if sig_ok && mac fk th_pre = sf then
         let th_sf = B.append th_pre sf in
         let i' = IdxFinishedKey (hs_index k ClientTraffic th_sh) in
         let st2 = { st1 with log = LKey i' :: st1.log } in
         (match o i' with
          | Some fkc ->
            (set_session st2 s (ClientSession (g, peer, CAccepted (k, th_sh, th_sf, not corrupt))),
             RClientFinished (mac fkc th_sf))
          | None -> (set_session st2 s (ClientSession (g, peer, CFailed)), RFail))
       else (failed, RFail)
     | None -> (failed, RFail))
  | _ -> (st, RFail)

let step_client_finished (o:key_oracle) (st:game_state) (s:nat) (cf:B.bytes)
  : GTot (game_state & response) =
  match session_at st s with
  | Some (ServerSession (g, id, SWaitFinished (k, th_sh, th_sf))) ->
    let i = IdxFinishedKey (hs_index k ClientTraffic th_sh) in
    let st1 = { st with log = LKey i :: st.log } in
    (match o i with
     | Some fkc ->
       if mac fkc th_sf = cf
       then (set_session st1 s (ServerSession (g, id, SAccepted (k, th_sh, th_sf))), RAccept true)
       else (set_session st1 s (ServerSession (g, id, SFailed)), RAccept false)
     | None -> (set_session st1 s (ServerSession (g, id, SFailed)), RAccept false))
  | _ -> (st, RFail)

(** Reveal of the handshake record key and IV. *)
let step_reveal_record_keys
  (o:key_oracle) (st:game_state) (s:nat) (label:traffic_label) (alg:C.aead_alg)
  : GTot (game_state & response) =
  match session_at st s with
  | Some x ->
    (match session_traffic_index x TrafficHandshake label with
     | Some t ->
       let ik = IdxAeadKey (alg, t) in
       let iv = IdxAeadIV t in
       ({ st with log = LKey iv :: LKey ik :: st.log }, RRecordKeys (o ik, o iv))
     | None -> (st, RRecordKeys (None, None)))
  | None -> (st, RRecordKeys (None, None))

(** Reveal of an application traffic secret; refused on the tested index. *)
let step_reveal (o:key_oracle) (st:game_state) (s:nat) (label:traffic_label)
  : GTot (game_state & response) =
  match session_at st s with
  | Some x ->
    (match session_traffic_index x TrafficApplication label with
     | Some t ->
       if st.tested = Some t then (st, RKey None)
       else
         ({ st with revealed = t :: st.revealed; log = LKey (IdxTraffic t) :: st.log },
          RKey (o (IdxTraffic t)))
     | None -> (st, RKey None))
  | None -> (st, RKey None)

(** Test of an application traffic secret of an authenticated client; at most
    once, and refused on a revealed index. *)
let step_test (a:answer_oracle) (st:game_state) (s:nat) (label:traffic_label)
  : GTot (game_state & response) =
  match session_at st s, st.tested with
  | Some (ClientSession (_, _, CAccepted (k, _, th_sf, true))), None ->
    let t = app_index k label th_sf in
    if L.mem t st.revealed then (st, RKey None)
    else ({ st with tested = Some t; log = LTest t :: st.log }, RKey (a t))
  | _, _ -> (st, RKey None)

let step (cs:coins) (o:key_oracle) (a:answer_oracle) (q:query) (st:game_state)
  : GTot (game_state & response) =
  match q with
  | QStartClient (g, peer, ch) ->
    let n = L.length st.sessions in
    (add_session st (ClientSession (g, peer, CWaitServerHello ch)), RShare (share cs g n))
  | QServerHello (s, server_share, sh) -> step_server_hello cs st s server_share sh
  | QStartServer (g, id, client_share, ch, sh, ee_cert, cv) ->
    step_start_server cs o st g id client_share ch sh ee_cert cv
  | QServerFlight (s, ee_cert, cv, sf) -> step_server_flight o st s ee_cert cv sf
  | QClientFinished (s, cf) -> step_client_finished o st s cf
  | QCorrupt id -> ({ st with corrupted = id :: st.corrupted }, ROk)
  | QRevealRecordKeys (s, label, alg) -> step_reveal_record_keys o st s label alg
  | QReveal (s, label) -> step_reveal o st s label
  | QTest (s, label) -> step_test a st s label

(** [n] rounds of the adversary against the game; returns the final state
    and the adversary's view (latest response first). *)
let rec run (cs:coins) (o:key_oracle) (a:answer_oracle) (adv:adversary) (n:nat)
  : GTot (game_state & list response) (decreases n) =
  if n = 0 then (initial_state, [])
  else
    let (st, v) = run cs o a adv (n - 1) in
    let (st', r) = step cs o a (adv v) st in
    (st', r :: v)
