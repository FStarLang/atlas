# atlas

Experimental TLS 1.3 client implementation in F*/Pulse, extracted to C. 


## Read next

- `calc_sample/CALC_DESIGN_AND_IMPL.md` - canonical calc-sample methodology reference.
- `TLS_OUTLINE.md` - concise task statement and proof requirements.
- `TLS_DESIGN_AND_IMPL.md` - canonical TLS design, proof plan, TCB, extraction notes, and validation workflow.

A proof of a TLS server is in progress and its design is currently in

- `TLS_SERVER_DESIGN_AND_IMPL.md` - TLS design extended to server with a key derivation agreement theorem

## Scope

The TLS proof target is the supported client profile: TLS 1.3, X25519,
`TLS_CHACHA20_POLY1305_SHA256`, basic 1-RTT handshakes, and application data.

Key exchange: the client offers the post-quantum hybrid X25519MLKEM768
(RFC 10024, group `0x11EC`) first, then X25519 and secp256r1, with a key share
for each.  The server prefers the hybrid when the ClientHello offers it next
to an X25519 share; otherwise it uses X25519 or secp256r1.  There is no
HelloRetryRequest.  The key-agreement theorems cover all three groups.  For
the hybrid they take one extra hypothesis, `tls_kex_agreement_ok`: ML-KEM-768
decapsulation recovers the encapsulated secret for the coins drawn.  This
fails with probability about 2^-164.  It is `True` for X25519 and secp256r1,
so the classical statement is the special case (see `KEY_AGREEMENT_PROOF.md`).
PSK, 0-RTT, resumption, client authentication, and key update are out of scope
for the current plan.

## Setup

### Dev container (recommended)

A `.devcontainer/` is provided. Opening the repository in a dev container (VS Code
"Reopen in Container", or `devcontainer up`) builds a minimal image and runs
`./setup.sh` automatically, producing a ready-to-build environment. To exercise
the whole pipeline (QuackyDucky generation → F* verification → C extraction
→ OpenSSL interop) from a clean checkout:

```sh
.devcontainer/test-full-path.sh
```

### Manual setup

```sh
./setup.sh
```

`./setup.sh` builds the EverParse toolchain (QuackyDucky + LowParse + the
F*/KaRaMeL binaries it vendors) from the pinned fork/commit into
`tools/everparse` (gitignored), then uses its F* to verify and extract the
[hacl-pulse](https://github.com/FStarLang/hacl-pulse) cryptographic library at
the commit pinned in `scripts/build-hacl-pulse.sh` into `tools/hacl-pulse`
(gitignored), and fetches the RFC and OpenSSL dependencies. No separate F* installation is required; the
`make` toolchain is derived from `EVERPARSE_HOME` (default `tools/everparse`).

Environment overrides: `EVERPARSE_HOME`, `EVERPARSE_REPO`, `EVERPARSE_BRANCH`,
`EVERPARSE_COMMIT`, `JOBS`, or point `FSTAR_EXE`/`KRML_EXE`/`QD_EXE` at a
different toolchain when invoking `make`.

## Validation

```sh
make parsers         # QuackyDucky: regenerate, verify, and extract the TLS wire
                     #   parsers/serializers from tls.qd.rfc (generated/)
make verify          # verify all F*/Pulse modules
make extract-tls13-bundle  # extract the unified client/server driver bundle
make test            # verify, check echo stubs, and run OpenSSL echo interop
make test-chromium-client-demo  # async HTTPS/1.1 Chromium adapter demo
make chromium-browser            # build Chromium with the verified provider
make test-chromium-browser       # actual browser HTTPS smoke test
make test-chromium-browser-public # network-dependent Google/Microsoft smoke
make chromium-browser-logging    # build Chromium with ATLAS JSONL tracing
make test-chromium-browser-logging # capture and analyze a browser trace
make chromium-demo-bundle        # transferable Linux x86_64 browser/server demo
make chromium-demo-bundle-logging # trace-capable transferable demo
make test-chromium-demo-bundle   # test the freshly extracted demo archive
```

The QuackyDucky pipeline can also be driven stage by stage with
`make regen-generated`, `make verify-generated`, and `make extract-generated`.

`make test-openssl-echo` runs the controlled local OpenSSL TLS 1.3 echo interop
scenario.  `make test-hybrid-interop` runs both verified endpoints against an
OpenSSL 3.5 peer using X25519MLKEM768.  The system OpenSSL 3.0 has no ML-KEM,
so build the 3.5 command-line tool first with `scripts/build-openssl35.sh`.
Without it the test is skipped. The main test sources live in `test/` and `test/unit/`.

The verified browser path is documented in `runtime/chromium/README.md`. It
includes the portable asynchronous adapter demo, a pinned Chromium overlay with
a concrete `net::SSLClientSocket`, and a transferable Linux x86_64
browser/server demo bundle; none gives the verified engine socket or browser
trust-policy ownership.

ATLAS tracing is compile-time controlled with `ATLAS_LOGGING=0` by default.
Logging builds emit connection-correlated JSONL metadata from verified
handshake, engine, and record-layer control flow. Analyze traces with
`runtime/analyze_atlas_trace.py`; see `runtime/chromium/README.md` for the trace
schema, safety boundary, and browser workflow.

For the methodology reference:

```sh
cd calc_sample
make verify
make check-admits
make test-c
```

## Shared protocol endpoint architecture

The calc sample and TLS runtime now share the same proof architecture in
`common/`:

- `Common.ProtocolImplementation` is the core refinement contract connecting
  Pulse network/local handlers, TCP byte histories, wire-format messages, and a
  state-machine step relation.
- `Common.ProtocolEndpoint` bundles that core implementation with a concrete
  `Common.TCP.channel`, persistent endpoint frames, network/local action
  resources, buffer preparation, and finish hooks. Driver-visible actions are
  first-order (`NeedInput`, `Local`, `Done`, `Failed`); callback outcomes are
  modeled as local/API events rather than external actions.
- `Common.ProtocolDriver` is a verified fuel-bounded endpoint loop. For C
  extraction, endpoint loops are specialized monomorphically: `calc_sample`
  extracts and runs a socket server through this structure, while the TLS C
  runtime wrappers call the generated endpoint/canonical functions directly for
  residual-buffered TLS I/O.

The main executable confidence gates are:

```sh
cd calc_sample && make test-c
make extract-tls13-bundle
make test-openssl-echo test-openssl-sclient
```
