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
| H3 `kex_group` gains `KexX25519MLKEM768`; `dh_group`; `TLS13.Crypto.Kex.Spec` (D2, `lemma_kex_agreement`) | **landed** (`5494f59`) |
| H4 `x25519mlkem768(0x11EC)` on the wire; ClientHello finder (1216) | **landed** (`f8bdbe4`) |
| H5a D4 as a type change: `ks_shared_secret : kex_shared_secret_any`, `optional_shared_secret_exactly` slot | **landed** (`bd04d41`) |
| H5b D1 fields, hybrid consistency clauses (D3), one key family per selection, `kex_group_of_named_group_full` | **landed** (`b7e9321`) |
| H6 model + proofs: hybrid ServerHello side arm, derive arms, D6 threaded to the System layers and the flagships | **landed** (`5e9a69f`) |
| H7 KEM-shaped runtime wrappers in `TLS13.KEX`; D4 64-byte shared-secret slot (`Repr.shared_secret_match`) | **landed** (`cf8f45a`) |
| H8a+b client offer: `poc_canonical_ch_g` / `client_hello_of_start` with an optional hybrid share, start storage (96-byte seed, 1216-byte share), gated generation behind the abstract `KEX.client_offers_hybrid`; Repr / `valid_start` pins removed | **landed** (`15b5d3f`) |
| H8c client: hybrid ServerHello (1120-byte share) parsing and storage, decaps / derive arm | **landed** (`500d9d4`) |
| H9a server: ClientHello hybrid share (1216 bytes) parsing and storage, `client_hello_hybrid_offered` metadata box | **landed** (`001533b`) |
| H9b server: driver key-exchange material widened from 64 to 128 bytes | **landed** (`719415e`) |
| H9c server: hybrid select / encaps / derive (64-byte secret) / ServerHello (1120-byte share) and driver dispatch, gated by `KEX.server_prefers_hybrid` | **landed** (`78d10d0`) |
| H10 flip: `client_offers_hybrid = server_prefers_hybrid = true`; `make test-hybrid-interop` (OpenSSL 3.5, both directions); docs | **landed** (this commit) |

H10 notes.  Both flags in `KEX.fst` are now `true`.  The `.fsti` keeps them
abstract, so the flip re-verifies only `TLS13.KEX`.  D6 already reaches the
flagships (H6), so there was no System change.
`test/interop/hybrid.sh` (`make test-hybrid-interop`, part of `make test`)
pins a system OpenSSL (>= 3.5) server to `-groups X25519MLKEM768` for the verified client.  For the verified
server it uses an OpenSSL 3.5 client sending hybrid and X25519 shares and
checks that the negotiated group is X25519MLKEM768.  It fails if the system
OpenSSL lacks ML-KEM.  Known limit: a ClientHello whose *only*
share is the hybrid is refused by the server.  The hybrid path requires
the ClientHello's (EC)DH pick to be X25519, and there is no
HelloRetryRequest.  OpenSSL 3.5, Chrome and Firefox all send an X25519 share
alongside the hybrid by default.

H9c notes.  The server's hybrid flight lives in
`BufferedHandshake.select_derive_send_hybrid_server_hello_from_payload_once`:
copy the random and the 64 bytes of encapsulation randomness from the
128-byte payload, read the stored 1216-byte client share, encapsulate
(`KEX.kex_hybrid_server_encaps_runtime`), select with
`server_hybrid_private = Some r` and the 1120-byte share (D3), derive the
64-byte secret, then send the ServerHello.  Encapsulation failure ends the
flight with `ServerFlightDeriveFailed` and an unchanged state.
`BufferedWorkflow.drive_handshake` takes this path only when
`KEX.server_prefers_hybrid` holds (false until H10) and the client offered
the hybrid; otherwise it runs the classical flight.  The supported-profile
predicate and `server_supported_groups` now include X25519MLKEM768.

H9b notes.  `driver_material_capacity` and every select / ServerHello payload
length is now 128 bytes, laid out as `[0,32)` server random, `[32,64)` DH
scalar, `[64,128)` hybrid encapsulation randomness (reserved; consumed in H9c).
The classical paths read only `[0,64)`, so behaviour is unchanged.

H9a notes.  `Messages.client_hello` gains a 1216-byte
`client_hello_hybrid_key_share` and a `has_hybrid` flag that
`is_valid_client_hello` pins to `Some? (CS.client_hello_hybrid_key_share ch)`.
The parser scans for the X25519MLKEM768 entry (`scan_ch_hybrid_key_share`,
first match wins); the acceptance gate is unchanged, so a ClientHello still
needs an X25519 or secp256r1 share.  `Repr.client_hello_slot_exactly` owns the
new vec and pins it to the offered share; a new metadata box
`client_hello_hybrid_offered` (conjunct `client_hello_hybrid_offered_exactly`)
records whether the offer was made, for the H9c group policy.  Both the server
(Network) and the client (LocalHandshake, via the serializer) fill the slot.

H8 notes.  `KEX.client_offers_hybrid` is a `val` in `KEX.fsti` (`false` in
`KEX.fst` until H10), so every client module is verified for both values.
With the hybrid offered, the ClientHello grows by 1222 bytes (2 in
`supported_groups`, 2 + 2 + 1216 for the KeyShareEntry): the handshake message
is at most 1761 bytes and the record 1766, so the `network_out_len` bound on
`LocalSendClientHello` goes from 544 to 1766 (the driver buffer is 20000).

H8c notes.  `Wire.Spec.serverHello_representable` accepts a ServerHello
whose only key share is the 1120-byte hybrid one.  `Messages.server_hello`
gains a 1120-byte `server_hello_hybrid_share` and an `is_hybrid` tag; the
parser scans for the hybrid entry (`scan_sh_hybrid_share`, first match wins).
`Repr.kex_share_storage` gains a 1120-byte `hybrid_share` slot, pinned by
`server_key_share_exactly` to `server_hybrid_bytes`, and the helper
`Repr.store_server_hello_key_shares` fills whichever slot the hello uses (it
is shared by `Network.mark_received_server_hello` and the server's
SH bookkeeping).  `LocalHandshake.try_derive_shared_secret` now tries the
(EC)DH arm first and, if that fails, the hybrid arm, which decapsulates using
`KEX.kex_hybrid_client_shared_runtime` and feeds the 64-byte secret to
`handshake_secret`.  To make this possible, `Model.derived_shared_secret_state`
takes a `kex_shared_secret_any`.  The server-side ensures, which are still
(EC)DH-only until H9, give their existential `shared` the type
`x25519_shared_secret`.

Re-staging made in H7: the hybrid start buffers (96-byte seed, 1216-byte
share) and the 1216/1120-byte hello slots (D5) are added with their first
user, so they move to H8 (client) and H9 (server).

Re-staging made in H5b: the `LocalDeriveSharedSecret` arms stay (EC)DH-only.
Opening the server arm to the KEM also changes
`server_x25519_pre_server_hello_projection` and the
`Some? server_key_share_private` facts that the impl ServerHello writer
consumes, so each KEM arm moves, with its H6 proof obligations, to the stage
that makes it reachable: H8 for the client arm (with `server_hello_kex`
accepting a 1120-byte share) and H9 for the server arm.  Until then a hybrid selection is *unsatisfiable* in the
server arm (it holds no DH private), so the model never reads it as X25519.

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

**As built (H6).**  D6 is
`Correspondence.paired_kex_agreement_ok client server`, which reads only the
two write-once fields `start_client_hybrid_private` and
`server_hybrid_private` (it is `True` until both are `Some`), and
`System.tls_kex_agreement_ok s` lifts it to a system state.  It is *not* added
to FACT 3: FACT 3 is inductive and D6 is not provable.  Instead:

* FACT 4 (`protected_witnesses_ok`) carries it as an antecedent;
* the app/stream invariants (`stream2_combined_inv`, `stream3_combined_inv`)
  are guarded by `tls_no_rekeying s /\ tls_kex_agreement_ok s`, exactly like
  the existing no-rekeying guard, and the preservation lemmas take D6 of the
  post-state;
* `lemma_kex_agreement_backward` transports D6 from post- to pre-state along
  any step (the fields are write-once, given `tls_system_inv` of the
  pre-state), which is what keeps the guarded invariants inductive;
* the flagships (`System.Temporal`, `System.StreamTemporal`) gain
  `tls_kex_agreement_ok s` in their antecedents.

**Side-arm deviation from D2 (H6).**  The (EC)DH accessors
(`server_hello_kex`, `server_selected_kex_group`, the DH privates) keep their
`dh_group` typing.  A hybrid ServerHello is read by separate accessors
(`serverHello_hybrid_share`, `server_hello_hybrid_share`, exclusive with
`server_hello_kex` by SMTPat lemmas), and a hybrid selection has `None` DH
privates.  This avoided re-typing every DH proof site.  Until H9 the impl
pins the server runtime to non-hybrid: `Repr.server_selection_private_absent`
carries `not (server_selects_hybrid selection)`.  (The client pin,
`None? start_client_hybrid_private` in `Repr.handshake_start_fields_exactly`,
was removed in H8.)

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

X25519MLKEM768 interop needs OpenSSL ≥ 3.5.  The dev container (Ubuntu 26.04)
ships OpenSSL 3.5 as the system OpenSSL, and the hybrid interop tests use it
unconditionally.  Sites that enumerate groups:

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
