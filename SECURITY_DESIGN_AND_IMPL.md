# Computational security of the TLS 1.3 key exchange: design and status

This document is the plan and status record for proving secrecy of the keys
derived by the atlas TLS 1.3 handshake, in a computational model, in F*.

The existing theorems (`KEY_AGREEMENT_PROOF.md`, `PAIRING_THEOREM.md`) are
functional: honest client and server derive the same keys. They say nothing
about what an attacker can learn. This work adds that.

## Target statement

Model: a multi-session game with an active network adversary. The adversary
starts honest client and server sessions, schedules and rewrites all messages,
and may corrupt long-term signing keys. The target property is key
indistinguishability.

For a *test* session, the adversary may ask for either the real or a random
key. The test session must be a client session that accepted an application
traffic secret from a server whose signing key was uncorrupted when the
session accepted. No partner session's key may have been revealed. The
adversary's view in the real-key and random-key worlds is then
indistinguishable, under the assumptions below.

First milestone:

- server authentication only;
- (EC)DH groups only (the index layer already covers X25519 and P-256);
- no PSK, 0-RTT or KeyUpdate;
- the X25519MLKEM768 hybrid is out of scope.

## Approach

We use miTLS-style ideal modules with non-interference proofs in F*, on top of
the existing spec. The spec in `src/spec/core` is not modified.

The step from real to ideal is per primitive. Each step is a standard
reduction, argued on paper and listed below. F* proves the protocol-level
content:

1. **Faithfulness.** Against the real oracles, the game runs the spec.
2. **Authentication.** A client that accepts with an honest server key is
   partnered on an honest exchange.
3. **Non-interference.** With ideal oracles, the adversary's view does not
   depend on the test key.

Symbolic (Dolev-Yao) tools such as DY* were considered and ruled out. DY* is
unmaintained and does not fit the Comparse-based wire formats.

## Layers (`src/spec/security/`)

| Module | Status | Content |
|---|---|---|
| `TLS13.Security.Index` | done | Public indices: `kex_index` (group + both shares), `traffic_index` (exchange, epoch, label, transcript **bytes**), `secret_index`. `real_secret dhe i` is the real key schedule from the (EC)DHE output. |
| `TLS13.Security.KeyIndex` | done | **Key-index lemma.** In every reachable (`connection_state_consistent`) client or non-failed server with a DH shared secret, the following are the real values at the state's public indices: the shared, handshake and master secrets; the installed handshake traffic key/IV; and the application traffic key/IV while there is no KeyUpdate. The (EC)DHE output is the DH of the endpoint's own ephemeral key with the peer's share on the wire. |
| `TLS13.Security.Oracle` | done | `key_oracle` (secrets by index), `real_oracle` over a (EC)DHE table, and `true_dhe_table`. `session_coherent o st` says every secret of a session is the oracle's value. The real oracle is coherent with every reachable session. |
| `TLS13.Security.Game` | done | Stage 2 multi-session key-indistinguishability game, parametric in the key oracle and the Test answer (see below). |
| `TLS13.Security.KeyIndistinguishability` | done | Stage 2 theorems: oracle locality, freshness/authentication invariant, ideal-world key indistinguishability. |

Indices use transcript bytes, not hashes. Collapsing them to hashes is
exactly the SHA-256 collision-resistance step, so keeping bytes makes that
assumption explicit.

## The stage-2 game (`TLS13.Security.Game`)

The game is a multi-session key exchange with server authentication.

- **Ephemeral keys.** Session number `n` uses ephemeral key `coins n`, for
  clients and servers alike.
- **Queries.** The adversary is an arbitrary deterministic function of its
  view. It issues:
  - `QStartClient` and `QStartServer`;
  - message deliveries: `QServerHello`, `QServerFlight`, `QClientFinished`;
  - `QCorrupt id` on a server identity;
  - `QRevealRecordKeys`: the handshake AEAD key and IV of any session;
  - `QReveal`: an application traffic secret;
  - `QTest`, at most once, on an application traffic secret of a client that
    accepted with an identity that was uncorrupted at acceptance.
- **Message contents.** The adversary supplies all public message contents
  (ClientHello / ServerHello / EE..Cert / CertificateVerify bytes), so it is
  at least as strong as a real network attacker. Transcripts are byte
  concatenations of these.
- **Ideal signatures (H5).** A server logs `(identity, {exchange; transcript
  up to CV})`. A client accepts a CertificateVerify for an uncorrupted
  identity only if that entry is logged; for a corrupted identity it accepts
  anything.
- **Finished MACs.** These are `HMAC(fk, Hash(transcript))`, with `fk` from
  the oracle at `IdxFinishedKey`.
- **Oracle use.** Every key the game uses is an oracle query at a public
  index, logged in the game state. Each query is one of:
  - finished keys;
  - handshake record keys and IVs;
  - application traffic secrets (Reveal);
  - the Test answer.
- **Freshness, enforced by the game.** Test refuses a revealed index, and
  Reveal refuses the tested index. The partner of the test session shares
  its index, so this covers partner reveals too.
- **Handshake traffic secrets are never revealed.** The finished keys derive
  from them, so the H2 hop (traffic secret as PRF key) needs them hidden.
  Revealing the record keys instead suffices to simulate the encrypted
  handshake record layer.

### Theorems (`TLS13.Security.KeyIndistinguishability`)

- `lemma_run_local`: two runs are equal if their oracles and Test answers
  agree at every logged query.
- `lemma_run_inv` / `lemma_tested_fresh`: if the adversary tested index
  `tt`, then:
  - `IdxTraffic tt` was never queried as a key, and `tt` is the only Test
    query;
  - the exchange of `tt` is **honest**: both shares come from game coins.
    The client share is the test session's own. The server share comes from
    the ideal-signature log, which only honest server sessions write. This
    is the authentication argument.
- `theorem_key_indistinguishability`: take the ideal oracle, which answers
  every honest-exchange index from a tape. Then the random-key run on `tape`
  with answer `r` equals the real-key run on `resample tape tt r`. With no
  test, the two worlds coincide.
- `lemma_random_world_independent`: the random-key run, and hence the choice
  of `tt`, does not depend on `tape` at `IdxTraffic tt`.

These last two lemmas give the probabilistic conclusion. Take a uniform tape
of independent entries. Resampling the coordinate at `tt` with a fresh
uniform `r` leaves the distribution unchanged, because `tt` is determined by
the other coordinates. Hence the real-key and random-key worlds are
**identically distributed**: the ideal game is perfectly secure. The step
from the theorem to the probability statement is the only part argued on
paper.

### Relation to the spec (stage 0)

The game is an abstraction of the spec's handshake. `TLS13.Security.Oracle`
and `TLS13.Security.KeyIndex` show that the spec's keys are the real oracle's
values at the same public indices, so with `real_oracle` the game's keys are
the spec's keys. The game does not yet replay full spec traces; see the
roadmap.

## Paper reductions (the hops)

Each hop replaces a real oracle by an ideal one at honest indices.

| # | Primitive | Assumption | Replaces |
|---|---|---|---|
| H1 | X25519 / P-256 | PRF-ODH (or GDH in ROM) for HKDF-Extract keyed by DHE | `IdxHandshake k` for honest `k` (both shares from honest ephemerals) |
| H2 | HKDF-Extract / Expand | dual-PRF / PRF | `IdxMaster`, `IdxTraffic`, `IdxAeadKey`, `IdxAeadIV`, `IdxFinishedKey` |
| H3 | SHA-256 | collision resistance | distinct transcripts ⇒ distinct hash inputs (justifies byte indices) |
| H4 | HMAC-SHA256 | PRF / EUF-CMA | Finished verification by table |
| H5 | Signature scheme | EUF-CMA | CertificateVerify verification for uncorrupted keys. Also uses the fact that the CV-signed transcript encodes both key shares (injective message formats), so signing `Hash(transcript)` determines the game's `{exchange; transcript}` content (with H3) |
| H6 | ChaCha20-Poly1305 | IND-CPA + INT-CTXT | (optional) record layer, for AEAD-key secrecy beyond key indistinguishability |

## Roadmap

1. ~~Stage 0a: index vocabulary and key-index lemma.~~
2. ~~Stage 0b: key-oracle abstraction and real-oracle coherence.~~
3. ~~Stage 2a: game, ideal oracle, honest indices.~~
4. ~~Stage 2b: authentication (tested exchange is honest via ideal signatures).~~
5. ~~Stage 2c: non-interference / key indistinguishability in the ideal world.~~
6. Stage 0c: faithfulness. Show that a real-oracle game run corresponds to
   legal spec executions of its honest sessions (`connection_state_consistent`
   shadows). This means constructing spec events from game steps, using
   `KeyIndex` for the key-dependent fields.
7. Matching conversations: an accepting client has a unique honest server
   session with the same transcript. This needs distinct ephemeral shares,
   a bad event of negligible probability.
8. Optional: ideal AEAD, for record-layer confidentiality and integrity, and
   KeyUpdate epochs.

## Known limitations

- **Failed servers.** The server key-index lemma excludes `ControlFailed`.
  A server can fail between deriving the shared secret and sending the
  ServerHello, and then the exchange has no public index. Such a session
  never emits keyed output, so the game need not route it.
- **KeyUpdate.** After a KeyUpdate the application slots hold iterates of the
  first-epoch secret (`KeyMaterial.application_traffic_secret_after`). These
  are not indexed yet.
- **Paper reductions.** The reductions are not mechanized. A full
  mechanization (Stage 3: SSP/pRHL-style) is future work.

## Validation

```
make _cache/TLS13.Security.KeyIndistinguishability.fst.checked   # checks all security modules
make check-admits                                # must report 0
```
