module TLS13.Security.KeyIndistinguishability

(**
  The stage-2 security theorem for [TLS13.Security.Game].

  Three facts, all proved here:

  1. Locality ([lemma_run_local]).  A run depends on the key oracle and on
     the Test answer only at the points recorded in the game's query log.

  2. Freshness and authentication ([lemma_run_inv]).  The game invariant says
     the following.  The tested index is never queried as a key: it was not
     revealed before the Test, and Reveal refuses it afterwards.  The tested
     exchange is honest: the client share is the tested session's own, and
     the server share belongs to an honest server session.  The latter holds
     because the client accepted a CertificateVerify for an identity that was
     uncorrupted when it accepted, and only honest server sessions log
     signatures.

  3. Key indistinguishability ([theorem_key_indistinguishability]).  In the
     ideal world (honest indices answered from a random tape) the following
     two runs are identical: the random-key world with tape [tape] and
     answer [r], and the real-key world with [tape] resampled to [r] at the
     test index.  Uniformly resampling one independent coordinate of a
     uniform tape preserves its distribution, and the test index does not
     depend on that coordinate ([lemma_random_world_independent]).  So the
     real-key and random-key worlds are identically distributed: the ideal
     game is perfectly secure.
**)

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module L = FStar.List.Tot

open TLS13.Spec.StateMachine
open TLS13.Security.Index
open TLS13.Security.Oracle
open TLS13.Security.Game

#set-options "--fuel 2 --ifuel 2 --z3rlimit 40"

(** {1 Locality} *)

let agree (o1 o2:key_oracle) (a1 a2:answer_oracle) (l:list logged) : prop =
  forall e. L.memP e l ==>
    (match e with
     | LKey i -> o1 i == o2 i
     | LTest t -> a1 t == a2 t)

let log_extends (st st':game_state) : prop =
  forall e. L.memP e st.log ==> L.memP e st'.log

let lemma_step_log_extends (cs:coins) (o:key_oracle) (a:answer_oracle) (q:query) (st:game_state)
  : Lemma (log_extends st (fst (step cs o a q st)))
=
  ()

let lemma_step_local
  (cs:coins) (o1 o2:key_oracle) (a1 a2:answer_oracle) (q:query) (st:game_state)
  : Lemma
      (requires agree o1 o2 a1 a2 (fst (step cs o1 a1 q st)).log)
      (ensures step cs o1 a1 q st == step cs o2 a2 q st)
=
  ()

let rec lemma_run_local
  (cs:coins) (o1 o2:key_oracle) (a1 a2:answer_oracle) (adv:adversary) (n:nat)
  : Lemma
      (requires agree o1 o2 a1 a2 (fst (run cs o1 a1 adv n)).log)
      (ensures run cs o1 a1 adv n == run cs o2 a2 adv n)
      (decreases n)
=
  if n = 0 then ()
  else begin
    let (st, v) = run cs o1 a1 adv (n - 1) in
    lemma_step_log_extends cs o1 a1 (adv v) st;
    lemma_run_local cs o1 o2 a1 a2 adv (n - 1);
    lemma_step_local cs o1 o2 a1 a2 (adv v) st
  end

(** {1 Honest exchanges} *)

(** [sh] is the share of one of the first [n] game coins. *)
let rec honest_share (cs:coins) (g:C.dh_group) (n:nat) (sh:B.bytes)
  : GTot bool (decreases n) =
  if n = 0 then false
  else share cs g (n - 1) = sh || honest_share cs g (n - 1) sh

(** Both shares of the exchange come from game coins. *)
let honest_kex (cs:coins) (n:nat) (k:kex_index) : GTot bool =
  honest_share cs k.kx_group n k.kx_client_share &&
  honest_share cs k.kx_group n k.kx_server_share

let rec lemma_honest_share_mono (cs:coins) (g:C.dh_group) (n m:nat) (sh:B.bytes)
  : Lemma
      (requires honest_share cs g n sh /\ n <= m)
      (ensures honest_share cs g m sh)
      (decreases m)
=
  if m = n then () else lemma_honest_share_mono cs g n (m - 1) sh

let rec lemma_honest_share_intro (cs:coins) (g:C.dh_group) (n s:nat)
  : Lemma
      (requires s < n)
      (ensures honest_share cs g n (share cs g s))
      (decreases n)
=
  if s = n - 1 then () else lemma_honest_share_intro cs g (n - 1) s

(** {1 Invariant} *)

let session_ok (cs:coins) (m:nat) (s:nat) (x:session) : GTot prop =
  match x with
  | ClientSession (g, _, CWaitFlight (k, _)) ->
    k.kx_group == g /\ k.kx_client_share == share cs g s
  | ClientSession (g, _, CAccepted (k, _, _, auth)) ->
    k.kx_group == g /\ k.kx_client_share == share cs g s /\
    (auth ==> honest_share cs g m k.kx_server_share)
  | _ -> True

let sessions_ok (cs:coins) (m:nat) (l:list session) : GTot prop =
  forall (s:nat). s < L.length l ==> session_ok cs m s (L.index l s)

let sig_ok (cs:coins) (m:nat) (e:ident & sig_content) : GTot prop =
  honest_share cs (snd e).sig_kex.kx_group m (snd e).sig_kex.kx_server_share

let sigs_ok (cs:coins) (m:nat) (l:list (ident & sig_content)) : GTot prop =
  forall e. L.memP e l ==> sig_ok cs m e

let fresh_ok (cs:coins) (st:game_state) : GTot prop =
  (forall t. L.memP (LKey (IdxTraffic t)) st.log ==> L.memP t st.revealed) /\
  (match st.tested with
   | None -> forall t. ~(L.memP (LTest t) st.log)
   | Some tt ->
     ~(L.memP tt st.revealed) /\
     honest_kex cs (L.length st.sessions) tt.ti_kex /\
     (forall t. L.memP (LTest t) st.log ==> t == tt))

let inv (cs:coins) (st:game_state) : GTot prop =
  let n = L.length st.sessions in
  sessions_ok cs n st.sessions /\
  sigs_ok cs n st.sig_log /\
  fresh_ok cs st

(** {2 Structural lemmas} *)

let lemma_session_ok_mono (cs:coins) (n m:nat) (s:nat) (x:session)
  : Lemma
      (requires session_ok cs n s x /\ n <= m)
      (ensures session_ok cs m s x)
=
  match x with
  | ClientSession (g, _, CAccepted (k, _, _, true)) ->
    lemma_honest_share_mono cs g n m k.kx_server_share
  | _ -> ()

let lemma_sessions_ok_mono (cs:coins) (n m:nat) (l:list session)
  : Lemma
      (requires sessions_ok cs n l /\ n <= m)
      (ensures sessions_ok cs m l)
=
  let aux (s:nat) : Lemma (s < L.length l ==> session_ok cs m s (L.index l s)) =
    if s < L.length l then lemma_session_ok_mono cs n m s (L.index l s)
  in
  FStar.Classical.forall_intro aux

let lemma_sigs_ok_mono (cs:coins) (n m:nat) (l:list (ident & sig_content))
  : Lemma
      (requires sigs_ok cs n l /\ n <= m)
      (ensures sigs_ok cs m l)
=
  let aux (e:ident & sig_content) : Lemma (L.memP e l ==> sig_ok cs m e) =
    FStar.Classical.move_requires
      (lemma_honest_share_mono cs (snd e).sig_kex.kx_group n m)
      (snd e).sig_kex.kx_server_share
  in
  FStar.Classical.forall_intro aux

let lemma_honest_kex_mono (cs:coins) (n m:nat) (k:kex_index)
  : Lemma
      (requires honest_kex cs n k /\ n <= m)
      (ensures honest_kex cs m k)
=
  lemma_honest_share_mono cs k.kx_group n m k.kx_client_share;
  lemma_honest_share_mono cs k.kx_group n m k.kx_server_share

let lemma_sessions_ok_update (cs:coins) (m:nat) (l:list session) (s:nat) (x:session)
  : Lemma
      (requires sessions_ok cs m l /\ s < L.length l /\ session_ok cs m s x)
      (ensures sessions_ok cs m (update_nth l s x))
=
  let aux (j:nat)
    : Lemma (j < L.length (update_nth l s x) ==>
             session_ok cs m j (L.index (update_nth l s x) j)) =
    if j < L.length l then lemma_update_nth_index l s x j
  in
  FStar.Classical.forall_intro aux

let lemma_sessions_ok_snoc (cs:coins) (m:nat) (l:list session) (x:session)
  : Lemma
      (requires sessions_ok cs m l /\ session_ok cs m (L.length l) x)
      (ensures sessions_ok cs m (L.append l [x]) /\
               L.length (L.append l [x]) == L.length l + 1)
=
  L.append_length l [x];
  let aux (j:nat)
    : Lemma (j < L.length (L.append l [x]) ==>
             session_ok cs m j (L.index (L.append l [x]) j)) =
    if j <= L.length l then lemma_snoc_index l x j
  in
  FStar.Classical.forall_intro aux

(** Adding a session: everything already established stays valid at the
    larger bound. *)
let lemma_inv_add_session (cs:coins) (st:game_state) (x:session)
  : Lemma
      (requires
        (let n = L.length st.sessions in
         sessions_ok cs n st.sessions /\
         sigs_ok cs (n + 1) st.sig_log /\
         fresh_ok cs st /\
         session_ok cs (n + 1) n x))
      (ensures inv cs (add_session st x))
=
  let n = L.length st.sessions in
  lemma_sessions_ok_mono cs n (n + 1) st.sessions;
  lemma_sessions_ok_snoc cs (n + 1) st.sessions x;
  match st.tested with
  | Some tt -> lemma_honest_kex_mono cs n (n + 1) tt.ti_kex
  | None -> ()

(** {2 Step preservation} *)

let lemma_inv_server_hello (cs:coins) (st:game_state) (s:nat) (server_share sh:B.bytes)
  : Lemma
      (requires inv cs st)
      (ensures inv cs (fst (step_server_hello cs st s server_share sh)))
=
  match session_at st s with
  | Some (ClientSession (g, peer, CWaitServerHello ch)) ->
    let k = { kx_group = g; kx_client_share = share cs g s; kx_server_share = server_share } in
    lemma_sessions_ok_update cs (L.length st.sessions) st.sessions s
      (ClientSession (g, peer, CWaitFlight (k, B.append ch sh)))
  | _ -> ()

let lemma_inv_start_server
  (cs:coins) (o:key_oracle) (st:game_state)
  (g:C.dh_group) (id:ident) (client_share ch sh ee_cert cv:B.bytes)
  : Lemma
      (requires inv cs st)
      (ensures inv cs (fst (step_start_server cs o st g id client_share ch sh ee_cert cv)))
=
  let n = L.length st.sessions in
  let k = { kx_group = g; kx_client_share = client_share; kx_server_share = share cs g n } in
  let th_sh = B.append ch sh in
  let th_cv = B.append th_sh ee_cert in
  let th_pre = B.append th_cv cv in
  let i = IdxFinishedKey (hs_index k ServerTraffic th_sh) in
  let st1 = { st with log = LKey i :: st.log } in
  lemma_sigs_ok_mono cs n (n + 1) st.sig_log;
  match o i with
  | Some fk ->
    let sf = mac fk th_pre in
    let e = (id, { sig_kex = k; sig_transcript = th_cv }) in
    let st2 = { st1 with sig_log = e :: st1.sig_log } in
    lemma_honest_share_intro cs g (n + 1) n;
    assert (sigs_ok cs (n + 1) st2.sig_log);
    lemma_inv_add_session cs st2 (ServerSession (g, id, SWaitFinished (k, th_sh, B.append th_pre sf)))
  | None ->
    lemma_inv_add_session cs st1 (ServerSession (g, id, SFailed))

let lemma_inv_server_flight
  (cs:coins) (o:key_oracle) (st:game_state) (s:nat) (ee_cert cv sf:B.bytes)
  : Lemma
      (requires inv cs st)
      (ensures inv cs (fst (step_server_flight o st s ee_cert cv sf)))
=
  let n = L.length st.sessions in
  match session_at st s with
  | Some (ClientSession (g, peer, CWaitFlight (k, th_sh))) ->
    let th_cv = B.append th_sh ee_cert in
    let corrupt = L.mem peer st.corrupted in
    let content = { sig_kex = k; sig_transcript = th_cv } in
    L.mem_memP (peer, content) st.sig_log;
    let i = IdxFinishedKey (hs_index k ServerTraffic th_sh) in
    let i' = IdxFinishedKey (hs_index k ClientTraffic th_sh) in
    let th_sf = B.append (B.append th_cv cv) sf in
    lemma_sessions_ok_update cs n st.sessions s (ClientSession (g, peer, CFailed));
    if corrupt || L.mem (peer, content) st.sig_log then begin
      assert (session_ok cs n s (L.index st.sessions s));
      if not corrupt then assert (sig_ok cs n (peer, content));
      lemma_sessions_ok_update cs n st.sessions s
        (ClientSession (g, peer, CAccepted (k, th_sh, th_sf, not corrupt)))
    end
  | _ -> ()

let lemma_inv_client_finished (cs:coins) (o:key_oracle) (st:game_state) (s:nat) (cf:B.bytes)
  : Lemma
      (requires inv cs st)
      (ensures inv cs (fst (step_client_finished o st s cf)))
=
  let n = L.length st.sessions in
  match session_at st s with
  | Some (ServerSession (g, id, SWaitFinished (k, th_sh, th_sf))) ->
    lemma_sessions_ok_update cs n st.sessions s (ServerSession (g, id, SAccepted (k, th_sh, th_sf)));
    lemma_sessions_ok_update cs n st.sessions s (ServerSession (g, id, SFailed))
  | _ -> ()

let lemma_inv_test (cs:coins) (a:answer_oracle) (st:game_state) (s:nat) (label:traffic_label)
  : Lemma
      (requires inv cs st)
      (ensures inv cs (fst (step_test a st s label)))
=
  let n = L.length st.sessions in
  match session_at st s, st.tested with
  | Some (ClientSession (g, _, CAccepted (k, _, th_sf, true))), None ->
    let t = app_index k label th_sf in
    L.mem_memP t st.revealed;
    assert (session_ok cs n s (L.index st.sessions s));
    lemma_honest_share_intro cs g n s
  | _, _ -> ()

let lemma_inv_step (cs:coins) (o:key_oracle) (a:answer_oracle) (q:query) (st:game_state)
  : Lemma
      (requires inv cs st)
      (ensures inv cs (fst (step cs o a q st)))
=
  let n = L.length st.sessions in
  match q with
  | QStartClient (g, peer, ch) ->
    lemma_sigs_ok_mono cs n (n + 1) st.sig_log;
    lemma_inv_add_session cs st (ClientSession (g, peer, CWaitServerHello ch))
  | QServerHello (s, server_share, sh) -> lemma_inv_server_hello cs st s server_share sh
  | QStartServer (g, id, client_share, ch, sh, ee_cert, cv) ->
    lemma_inv_start_server cs o st g id client_share ch sh ee_cert cv
  | QServerFlight (s, ee_cert, cv, sf) -> lemma_inv_server_flight cs o st s ee_cert cv sf
  | QClientFinished (s, cf) -> lemma_inv_client_finished cs o st s cf
  | QCorrupt _ -> ()
  | QRevealRecordKeys _ -> ()
  | QReveal _ -> ()
  | QTest (s, label) -> lemma_inv_test cs a st s label

(** The non-creating steps only update sessions in place. *)
let same_length (st:game_state) (p:game_state & response) : prop =
  L.length (fst p).sessions == L.length st.sessions

let lemma_server_hello_length (cs:coins) (st:game_state) (s:nat) (server_share sh:B.bytes)
  : Lemma (same_length st (step_server_hello cs st s server_share sh))
= match session_at st s with
  | Some (ClientSession (g, peer, CWaitServerHello ch)) ->
    let k = { kx_group = g; kx_client_share = share cs g s; kx_server_share = server_share } in
    lemma_update_nth_length st.sessions s (ClientSession (g, peer, CWaitFlight (k, B.append ch sh)))
  | _ -> ()

let lemma_server_flight_length (o:key_oracle) (st:game_state) (s:nat) (ee_cert cv sf:B.bytes)
  : Lemma (same_length st (step_server_flight o st s ee_cert cv sf))
= match session_at st s with
  | Some (ClientSession (g, peer, CWaitFlight (k, th_sh))) ->
    let th_sf = B.append (B.append (B.append th_sh ee_cert) cv) sf in
    lemma_update_nth_length st.sessions s (ClientSession (g, peer, CFailed));
    lemma_update_nth_length st.sessions s
      (ClientSession (g, peer, CAccepted (k, th_sh, th_sf, not (L.mem peer st.corrupted))))
  | _ -> ()

let lemma_client_finished_length (o:key_oracle) (st:game_state) (s:nat) (cf:B.bytes)
  : Lemma (same_length st (step_client_finished o st s cf))
= match session_at st s with
  | Some (ServerSession (g, id, SWaitFinished (k, th_sh, th_sf))) ->
    lemma_update_nth_length st.sessions s (ServerSession (g, id, SAccepted (k, th_sh, th_sf)));
    lemma_update_nth_length st.sessions s (ServerSession (g, id, SFailed))
  | _ -> ()

let lemma_step_sessions_bound (cs:coins) (o:key_oracle) (a:answer_oracle) (q:query) (st:game_state)
  : Lemma (L.length (fst (step cs o a q st)).sessions <= L.length st.sessions + 1)
=
  match q with
  | QStartClient (g, peer, ch) ->
    L.append_length st.sessions [ClientSession (g, peer, CWaitServerHello ch)]
  | QStartServer (g, id, client_share, ch, sh, ee_cert, cv) ->
    let k = { kx_group = g; kx_client_share = client_share;
              kx_server_share = share cs g (L.length st.sessions) } in
    let th_sh = B.append ch sh in
    let th_pre = B.append (B.append th_sh ee_cert) cv in
    let i = IdxFinishedKey (hs_index k ServerTraffic th_sh) in
    (match o i with
     | Some fk ->
       L.append_length st.sessions
         [ServerSession (g, id, SWaitFinished (k, th_sh, B.append th_pre (mac fk th_pre)))]
     | None -> L.append_length st.sessions [ServerSession (g, id, SFailed)])
  | QServerHello (s, server_share, sh) ->
    lemma_server_hello_length cs st s server_share sh
  | QServerFlight (s, ee_cert, cv, sf) ->
    lemma_server_flight_length o st s ee_cert cv sf
  | QClientFinished (s, cf) ->
    lemma_client_finished_length o st s cf
  | _ -> ()

let rec lemma_run_inv (cs:coins) (o:key_oracle) (a:answer_oracle) (adv:adversary) (n:nat)
  : Lemma
      (ensures
        inv cs (fst (run cs o a adv n)) /\
        L.length (fst (run cs o a adv n)).sessions <= n)
      (decreases n)
=
  if n = 0 then ()
  else begin
    let (st, v) = run cs o a adv (n - 1) in
    lemma_run_inv cs o a adv (n - 1);
    lemma_inv_step cs o a (adv v) st;
    lemma_step_sessions_bound cs o a (adv v) st
  end

(** {1 Ideal world and the main theorem} *)

(** Honest indices are answered from the tape; the others by [real]. *)
let ideal_oracle
  (hon:kex_index -> GTot bool)
  (tape:secret_index -> GTot B.bytes)
  (real:key_oracle)
  : key_oracle =
  fun i -> if hon (secret_index_kex i) then Some (tape i) else real i

(** Test returns the oracle's own value (real-key world)... *)
let real_answers (o:key_oracle) : answer_oracle = fun t -> o (IdxTraffic t)

(** ...or an independent value [r] (random-key world). *)
let random_answers (r:B.bytes) : answer_oracle = fun _ -> Some r

(** The tape with the entry for the traffic secret [t] replaced by [r]. *)
let resample (tape:secret_index -> GTot B.bytes) (t:traffic_index) (r:B.bytes)
  : secret_index -> GTot B.bytes =
  fun i -> if i = IdxTraffic t then r else tape i

let random_world (cs:coins) (tape:secret_index -> GTot B.bytes) (real:key_oracle)
  (r:B.bytes) (adv:adversary) (n:nat) : GTot (game_state & list response) =
  run cs (ideal_oracle (honest_kex cs n) tape real) (random_answers r) adv n

let real_world (cs:coins) (tape:secret_index -> GTot B.bytes) (real:key_oracle)
  (adv:adversary) (n:nat) : GTot (game_state & list response) =
  let o = ideal_oracle (honest_kex cs n) tape real in
  run cs o (real_answers o) adv n

(** The only use of the tested index is the Test answer, and the tested
    exchange is honest at the oracle's bound. *)
let lemma_tested_fresh (cs:coins) (o:key_oracle) (a:answer_oracle) (adv:adversary) (n:nat)
  : Lemma
      (ensures (
        let st = fst (run cs o a adv n) in
        match st.tested with
        | Some tt ->
          honest_kex cs n tt.ti_kex /\
          ~(L.memP (LKey (IdxTraffic tt)) st.log) /\
          (forall t. L.memP (LTest t) st.log ==> t == tt)
        | None -> forall t. ~(L.memP (LTest t) st.log)))
=
  lemma_run_inv cs o a adv n;
  let st = fst (run cs o a adv n) in
  match st.tested with
  | Some tt -> lemma_honest_kex_mono cs (L.length st.sessions) n tt.ti_kex
  | None -> ()

(** Key indistinguishability in the ideal world.  If the adversary tests the
    index [tt], the random-key run on [tape] is identical to the real-key run
    on [tape] resampled to [r] at [tt]; if it never tests, the two worlds
    coincide on the same tape. *)
let theorem_key_indistinguishability
  (cs:coins) (tape:secret_index -> GTot B.bytes) (real:key_oracle)
  (r:B.bytes) (adv:adversary) (n:nat)
  : Lemma
      (ensures (
        let rw = random_world cs tape real r adv n in
        match (fst rw).tested with
        | Some tt -> real_world cs (resample tape tt r) real adv n == rw
        | None -> real_world cs tape real adv n == rw))
=
  let hon = honest_kex cs n in
  let o = ideal_oracle hon tape real in
  let a = random_answers r in
  lemma_tested_fresh cs o a adv n;
  let st = fst (run cs o a adv n) in
  match st.tested with
  | Some tt ->
    let o' = ideal_oracle hon (resample tape tt r) real in
    assert (agree o o' a (real_answers o') st.log);
    lemma_run_local cs o o' a (real_answers o') adv n
  | None ->
    assert (agree o o a (real_answers o) st.log);
    lemma_run_local cs o o a (real_answers o) adv n

(** The random-key world does not depend on the tape at the index it tests:
    the test index is a function of the other tape entries.  This is the
    side condition of the resampling argument. *)
let lemma_random_world_independent
  (cs:coins) (tape:secret_index -> GTot B.bytes) (real:key_oracle)
  (r r':B.bytes) (adv:adversary) (n:nat)
  : Lemma
      (ensures (
        let rw = random_world cs tape real r adv n in
        match (fst rw).tested with
        | Some tt -> random_world cs (resample tape tt r') real r adv n == rw
        | None -> True))
=
  let hon = honest_kex cs n in
  let o = ideal_oracle hon tape real in
  let a = random_answers r in
  lemma_tested_fresh cs o a adv n;
  let st = fst (run cs o a adv n) in
  match st.tested with
  | Some tt ->
    let o' = ideal_oracle hon (resample tape tt r') real in
    assert (agree o o' a a st.log);
    lemma_run_local cs o o' a a adv n
  | None -> ()
