# H1 implementation plan: X25519MLKEM768 (RFC 10024) on client and server

Scope, as agreed: the hybrid group **X25519MLKEM768 (0x11EC)** offered and
accepted **alongside** X25519 (and the existing secp256r1), on **both the client
and the server**, with the key-agreement and pairing theorems **fully verified**.
HelloRetryRequest and SecP256r1MLKEM768 / SecP384r1MLKEM1024 are out of scope
(hacl-pulse has no P-384).  The staging discipline is G2's
([server-p256-plan.md](server-p256-plan.md), D5): every commit is green, with
0 errors and 0 admits, and only the last stage turns the group on.

## Where to pick up

| stage | status |
| --- | --- |
| H1 crypto spec `TLS13.Crypto.Hybrid.Spec` | **landed** (`75000f8`) |
| H2 Pulse bindings `TLS13.Crypto.Hybrid` + KAT in `test_crypto` | **landed** (`75000f8`) |
| H3 … H10 | not started |

## 0. RFC 10024 facts the design depends on

* Client share = ML-KEM-768 `ek` (1184) ‖ X25519 public (32) = **1216** bytes.
* Server share = ML-KEM-768 ciphertext (1088) ‖ X25519 public (32) = **1120** bytes.
* Shared secret = ML-KEM ss (32) ‖ X25519 ss (32) = **64** bytes, and it is the
  `(EC)DHE` input to HKDF-Extract.
* ML-KEM comes first in all three.
* The server MUST run the FIPS 203 §7.2 modulus check on `ek`.  The client checks
  the ciphertext length.  Both sides reject an all-zero X25519 output.  All of
  these are `illegal_parameter`.
* The server's share **depends on the client's share** (encapsulation).  This is
  the one structural difference from (EC)DH, and it drives D2 below.

## 1. What H1/H2 provide (landed)

`src/spec/assumptions/TLS13.Crypto.Hybrid.Spec.fsti`:

* `x25519mlkem768_client_public csk`
* `x25519mlkem768_server_share ssk cs : option`
* `x25519mlkem768_server_shared ssk cs : option`
* `x25519mlkem768_client_shared csk ss : option`
* `lemma_x25519mlkem768_agreement`: an honest client share is always accepted,
  and both sides compute equal secrets *under* `mlkem768_correct_coins d z m`,
  the deterministic ML-KEM noise bound.

The spec is defined over hacl-pulse's `Spec.MLKEM`.  It adds no new axiom:
ML-KEM correctness fails with probability about 2^-164, and the theorem carries
that event as a hypothesis instead of assuming it away.

Private keys are seeds: the client's is `d ‖ z ‖ x25519` (96 bytes) and the
server's is `m ‖ x25519` (64 bytes).  The client regenerates `dk` at decaps time
rather than storing 2400 bytes.

`src/impl/TLS13.Crypto.Hybrid.fst(i)` holds the three Pulse functions, proved
equal to the spec.  Seeds and `dk` are wiped.  `test/unit/test_crypto.c`
checks them against kyber-py's FIPS 203 `*_internal` functions and RFC 7748, and
covers both rejection paths.

## 2. Design decisions

### D1 — additive per-group fields, exactly as G2's D1/D2

`handshake_start` gains `start_client_hybrid_private : option (bytes_of_len 96)`
and `start_client_hybrid_public : bytes_of_len 1216`.
`server_handshake_selection` gains `server_hybrid_private : option (bytes_of_len 64)`
and `server_hybrid_share : bytes_of_len 1120`.  `IM.client_hello` gains a
1216-byte slot.  The ~150 X25519/P-256 field occurrences keep their meaning and
their proofs.

### D2 — a KEM-shaped group interface in `TLS13.Crypto.Spec`

`kex_group` gains `KexX25519MLKEM768`.  The single DH-shaped pair
`kex_public_from_private g sk` / `kex_shared g sk pk` is replaced by
direction-explicit functions.  For the DH groups each is definitionally the old
one, so the X25519/P-256 arms of existing proofs go through by unfolding:

```fstar
kex_client_private_len g   (* 32 | 32 | 96 *)
kex_server_private_len g   (* 32 | 32 | 64 *)
kex_client_share_len g     (* 32 | 65 | 1216 *)
kex_server_share_len g     (* 32 | 65 | 1120 *)
kex_shared_len g           (* 32 | 32 | 64 *)
kex_client_public g csk                    : kex_client_share g
kex_server_share  g ssk client_share       : option (kex_server_share g)
kex_server_shared g ssk client_share       : option (kex_shared_secret g)
kex_client_shared g csk server_share       : option (kex_shared_secret g)
kex_agreement_ok  g csk ssk : prop          (* True | True | mlkem768_correct_coins *)
lemma_kex_agreement g csk ssk               (* requires kex_agreement_ok *)
```

**Rejected alternative:** keep `kex_shared g sk pk` and dispatch the hybrid on
`B.length sk` (96 means client, 64 means server).  It would save about 77
proof-site edits, but it re-introduces exactly the length-laundering that the
`kex_group` comment forbids.

### D3 — the server share is fixed at selection time

The server learns the client share before it builds the selection.  It can
therefore generate `ssk`, run `x25519mlkem768_server_encaps` and store
`server_hybrid_share` in the selection record.  The consistency predicate is
`kex_server_share g ssk (client_hello_kex ch g) == Some share`, replacing
`kex_public_from_private g sk == pub` for the hybrid.  A failed ek check means no
acceptable selection exists, which becomes `illegal_parameter`.

### D4 — the shared secret becomes variable width (32 or 64)

`ks_shared_secret : option C.x25519_shared_secret` becomes
`option (s:B.bytes{B.length s == 32 \/ B.length s == 64})`.  The key schedule
already takes `B.bytes` (`TLS13.Keys.handshake_secret`).  At runtime a
**64-byte buffer plus a length** follows the `pad_share_65` precedent: the
logical secret is the `kex_shared_len g` prefix, chosen by the group tag.
HKDF-Extract's `ikm_len` becomes `kex_shared_len g`.  This is the widest change
(about 45 files carry `LocalDeriveSharedSecret` / the 32-byte type) and is mostly
mechanical.

### D5 — wide share buffers

`pad_share_65` / `unpad_share_65` / `padded_share_65` become
`pad_share` / `unpad_share` / `padded_share` over a group-independent maximum
width.  That maximum is 1120 for ServerHello-side storage, while ClientHello
shares live in per-group slots (D1).

### D6 — the theorem statement gains one hypothesis

`lemma_flagship_record_material_agreement` (`System.Temporal.fst:82`) and FACT 3
(`hello_key_shares_ok`) gain `kex_agreement_ok g csk ssk` for the negotiated
group.  For X25519 and P-256 it is `True`, so the existing statement is the
special case.  This must be stated in README and KEY_AGREEMENT_PROOF.md.

## 3. Stages (each one green; the capability flips only in H10)

| stage | content | main files |
| --- | --- | --- |
| **H3** | D2 in `TLS13.Crypto.Spec`: new `kex_group` constructor and direction-explicit API; DH arms unfold to the old functions; `lemma_kex_agreement`.  Old names stay as DH-only aliases until H9. | `Crypto.Spec.fsti/.fst` (re-verifies the whole tree) |
| **H4** | Wire: `x25519mlkem768(0x11EC)` in `tls.qd.rfc`, `make regen-generated`; `Sem.kex_group_of_named_group`, `named_group_share_len` (direction-aware), `sh_find_kex_share` (1120), a client-side finder (1216), and the shape lemmas. | `tls.qd.rfc`, `generated/`, `Wire.Semantics.fst` |
| **H5** | Model: D1 fields; `start_kex_private/public`, `client_hello_kex`, `server_hello_kex`, `server_kex_*` re-typed per D2; `handshake_start_key_share_consistent`, `server_selection_key_share_consistent` (D3); `LocalDeriveSharedSecret` preconditions use `kex_client_shared` / `kex_server_shared`; D4 type of `ks_shared_secret`.  Record-literal fallout. | `Spec.StateMachine.fst`, `Wire.Spec.fst` (`ch_key_share_pick`), endpoints |
| **H6** | Proofs over the model: `ConnectionState.Lemmas` (`lemma_paired_x25519_key_shares_shared_secret_agree` → `lemma_kex_agreement`), `Correspondence`, `ServerHelloSelectionLink`, `HandshakeAgreementNonReady`, `ProtectedWire*` (shared-secret width). | `src/spec/properties/*` |
| **H7** | Runtime KEX: `TLS13.KEX` becomes KEM-shaped (`kex_client_public_runtime`, `kex_server_encaps_runtime`, `kex_client_shared_runtime`) over the H2 bindings; D5 buffers; D4 64-byte secret buffer and `ikm_len`. | `KEX.fst(i)`, `ConnectionState.Repr`, `LocalHandshake` |
| **H8** | Client: generate the 96-byte seed, compute the 1216-byte share, serialize a third KeyShareEntry (and `supported_groups`), store it, decaps on a hybrid ServerHello. | `LocalHandshake`, `Serializer.Handshake`, `Messages`, `Parser`, `Client*` |
| **H9** | Server: parse the 1216-byte offer; selection runs encaps (D3); `illegal_parameter` on ek failure; ServerHello with a 1120-byte share; widened driver payloads (`BufferedHandshake/Workflow`, `Server.Setup`, `Server.Keys`, `Server.Send`). | `Impl.Server*` |
| **H10** | Flip: client offers `[X25519MLKEM768, X25519, secp256r1]` and the server prefers the hybrid; System FACT 3 and the flagship theorem gain D6; tests and interop; docs (`tls.rfc`, README, KEY_AGREEMENT_PROOF.md, RESULTS.md). | `System*.fst`, `Repr.fsti` config, tests, docs |

### Size checks already done

* Wire bounds: `key_exchange<1..2^16-1>` and `client_shares<0..2^16-1>` accept
  the hybrid shares.
* ClientHello with three shares: about 1.5 to 1.8 KB.  That is below
  `max_client_hello_len = 8192` and the 16640 single-record bound, so neither
  constant changes.
* ServerHello: about 1.2 KB, a single record.
* Still to confirm in H9: the server driver's concrete receive capacities
  (`DS.driver_*_capacity`).

## 4. Interop

The system OpenSSL is 3.0.13, which has no ML-KEM.  X25519MLKEM768 interop needs
OpenSSL ≥ 3.5, so H10 must add an optional OpenSSL 3.5 build, either in
`setup.sh` or as a separate `scripts/` helper.  Hybrid cells must be skipped,
not failed, when it is absent.  Sites that enumerate groups:

* `test/unit/test_server_interop_matrix.c:74-80,775,815`
* `test/openssl_{http,echo}_server.c`
* `test/perf/tls13_bench.c`
* `test/interop/host_root.py:35`
* `test/interop/RESULTS.md`

## 5. Risks

* **H3 and H5 re-verify everything** (about 17 min at -j100).  Iterate per module
  with `make _cache/<M>.checked`.
* **The D4 width change is wide.**  It can be pre-staged as a type change with
  every value still 32 bytes before H7 makes 64 reachable, as G2's S6.7 did.
* **Proof stability.**  Follow G2's rules: no rlimit or seed bumps; name lemmas
  and add explicit asserts; never end a Pulse block on a lemma call where the
  postcondition needs its fact (rewrite explicitly, as in `TLS13.Crypto.Hybrid`).
