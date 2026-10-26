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
| `TLS13.Security.Game` | todo | Multi-session game, parameterized by the oracle (see below). |
| `TLS13.Security.Ideal*` | todo | Stage 2: ideal oracles and the non-interference and authentication theorems. |

Indices use transcript bytes, not hashes. Collapsing them to hashes is
exactly the SHA-256 collision-resistance step, so keeping bytes makes that
assumption explicit.

## Game design

- **Sessions.** Each honest session is a spec `connection_state`, the
  "shadow". Its ephemeral randomness is drawn by the game: the
  `handshake_start` / `server_handshake_selection` privates are game coins.
- **Oracle routing.** Every secret-dependent value the adversary can observe
  goes through the key oracle at the session's public index:
  - record protection keys;
  - Finished MACs;
  - accept/reject decisions.

  A server's CertificateVerify is produced by a signing oracle.
  Signing correctness (`verify (sign sk m)`) is a hypothesis of the
  oracle record, not an axiom; `make check-admits` must stay 0.
- **Adversary role.** The adversary chooses public message contents, such as
  extensions and certificate chains. The game fills in secret-dependent
  fields and checks public legality.
- **Real link (stage 0).** With `real_oracle (true_dhe_table ...)`, every
  honest shadow state is `connection_state_consistent` and canonical. This
  follows from `Oracle.lemma_*_coherent` and `KeyIndex`.
- **Ideal world (stage 2).** Shadow legality fails here: Finished checks
  against table keys do not satisfy the spec's real-crypto relations. So
  ideal-world invariants are stated over the game's public data, and the
  shadow is advanced with `step_model` only.

## Paper reductions (the hops)

Each hop replaces a real oracle by an ideal one at honest indices.

| # | Primitive | Assumption | Replaces |
|---|---|---|---|
| H1 | X25519 / P-256 | PRF-ODH (or GDH in ROM) for HKDF-Extract keyed by DHE | `IdxHandshake k` for honest `k` (both shares from honest ephemerals) |
| H2 | HKDF-Extract / Expand | dual-PRF / PRF | `IdxMaster`, `IdxTraffic`, `IdxAeadKey`, `IdxAeadIV`, `IdxFinishedKey` |
| H3 | SHA-256 | collision resistance | distinct transcripts ⇒ distinct hash inputs (justifies byte indices) |
| H4 | HMAC-SHA256 | PRF / EUF-CMA | Finished verification by table |
| H5 | Signature scheme | EUF-CMA | CertificateVerify verification for uncorrupted keys |
| H6 | ChaCha20-Poly1305 | IND-CPA + INT-CTXT | (optional) record layer, for AEAD-key secrecy beyond key indistinguishability |

## Roadmap

1. ~~Stage 0a: index vocabulary and key-index lemma.~~
2. ~~Stage 0b: key-oracle abstraction and real-oracle coherence.~~
3. Stage 0c: game definition and real-world faithfulness lemma.
4. Stage 2a: ideal oracle tables, and freshness of honest indices.
5. Stage 2b: authentication. An accepting client with an uncorrupted server
   key under the ideal signature has an honest `kex_index` and a matching
   server session.
6. Stage 2c: non-interference. The adversary view is identical for ideal
   tables differing only at the test session's application traffic indices.
7. Optional: ideal AEAD, for record-layer confidentiality and integrity.

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
make _cache/TLS13.Security.Oracle.fst.checked   # checks Index, KeyIndex, Oracle
make check-admits                                # must report 0
```
