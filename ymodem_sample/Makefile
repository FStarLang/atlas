# ═══════════════════════════════════════════════════════════════════
# YMODEM sample: Makefile (verify + C extraction)
# ═══════════════════════════════════════════════════════════════════
# Verifies the YMODEM reliable-delivery (ARQ) specification and executable layer,
# and extracts the verified codec leaf to C for the interop wrappers.
#
#   * Specification layer (spec/): the QuackyDucky-generated wire format (a
#     leading-byte-discriminated packet/control union `ymodem_message`), the
#     wire_format instance, and the stop-and-wait ARQ state-machine +
#     file_transfer instances (YModem.Protocol).
#
#   * Executable layer (impl/):
#       - YModem.Impl.Codec holds the executable *leaf* codecs:
#         `ymodem_emit_data_block` (serialize a Body_soh data packet) and
#         `ymodem_recv_data_block` (parse one).  They are standalone (only Pulse/
#         F* array primitives), fully VERIFIED against the QuackyDucky wire
#         format, and Custard extracts them to one small self-contained C file
#         with unprefixed names — the ABI the interop wrappers link against.  The
#         control frames (EOT/ACK/NAK/CAN/'C') are single literal bytes handled
#         directly in the wrappers, so they need no leaf.
#       - YModem.Impl.{Server,Client}.CanonicalProtocol hold the
#         Common.ProtocolImplementation.protocol_implementation instances (the
#         verified refinement witnesses for ymodem_{server,client}_wfsm) that
#         drive those leaves; YModem.Impl.{Server,Client}.Endpoint hold the
#         Common.ProtocolEndpoint instances, and YModem.Impl.{Server,Client}.Socket
#         the runners `ymodem_server_send` / `ymodem_client_receive`, which run
#         the shared Common.ProtocolDriver.drive_steps loop.  Custard
#         monomorphises the dictionaries away when extracting the runners
#         (`make extract-loops`).

# ── Toolchain ──────────────────────────────────────────────────────
EVERPARSE_HOME ?= $(abspath ../tools/everparse)
FSTAR_HOME ?= $(EVERPARSE_HOME)/opt/FStar
FSTAR_EXE ?= $(FSTAR_HOME)/bin/fstar.exe
QD ?= $(EVERPARSE_HOME)/bin/everparse-qd.exe
Z3_DIR ?= $(EVERPARSE_HOME)/opt/z3
LOWPARSE_HOME ?= $(EVERPARSE_HOME)/lib/everparse/lowparse
export PATH := $(Z3_DIR):$(PATH)

# Z3 version used by every F* invocation; see the root Makefile for why 4.15.3.
# Pinned in scripts/z3-version.txt at the repo root -- single source of truth
# shared with the root Makefile, scripts/install-z3.sh and the CI dev-container
# cache key.
Z3_VERSION_FILE ?= ../scripts/z3-version.txt
Z3_VERSION ?= $(strip $(shell cat $(Z3_VERSION_FILE)))
ifeq ($(Z3_VERSION),)
$(error Could not read the pinned Z3 version from $(Z3_VERSION_FILE))
endif

# ── Directories ────────────────────────────────────────────────────
CACHE_DIR   = _cache
SPEC_DIR    = spec
IMPL_DIR    = impl
EXTERN_DIR  = ../src/impl/extern
OUTPUT_DIR  = _output
EXTRACT_DIR = _extract

# ── F* Flags ───────────────────────────────────────────────────────
INCLUDES = \
  --include ../common \
  --include $(EXTERN_DIR) \
  --include $(LOWPARSE_HOME) \
  --include $(SPEC_DIR) \
  --include $(IMPL_DIR)

FSTAR_FLAGS = \
  --z3version $(Z3_VERSION) \
  --cache_checked_modules \
  --cache_dir $(CACHE_DIR) \
  --odir $(OUTPUT_DIR) \
  --already_cached 'Prims,FStar,Pulse,PulseCore,C,Spec.Loops,LowParse' \
  --warn_error -321-241-272-288 \
  --report_assumes warn \
  --ext optimize_let_vc \
  --ext fly_deps \
  $(INCLUDES)

FSTAR = $(FSTAR_EXE) $(FSTAR_FLAGS)

# ── Source Files ───────────────────────────────────────────────────
COMMON_FILES = $(wildcard ../common/*.fst ../common/*.fsti)
EXTERN_FILES = $(EXTERN_DIR)/Common.Memmove.fsti
SPEC_FILES = $(wildcard $(SPEC_DIR)/*.fst $(SPEC_DIR)/*.fsti)
IMPL_FILES = $(wildcard $(IMPL_DIR)/*.fst $(IMPL_DIR)/*.fsti)
ALL_FILES  = $(COMMON_FILES) $(EXTERN_FILES) $(SPEC_FILES) $(IMPL_FILES)

.PHONY: all verify gen extract extract-c wrappers clean check-admits help

all: verify

# ── Dependency Analysis ────────────────────────────────────────────
.depend: $(ALL_FILES)
	@echo "Generating dependencies..."
	@$(FSTAR) --dep full $(ALL_FILES) --output_deps_to $@

-include .depend

# ── Generic Verification Rules ────────────────────────────────────
$(CACHE_DIR)/%.checked: | $(CACHE_DIR)
	@echo "Verifying $<"
	@$(FSTAR) $<
	@touch $@

$(CACHE_DIR):
	@mkdir -p $@

verify: $(ALL_CHECKED_FILES)
	@echo "All YMODEM modules verified"

check-admits:
	@echo "Checking for admits (the codec leaves are verified; CanonicalProtocol instances too)..."
	@grep -rn "admit *()" $(IMPL_DIR) 2>/dev/null || echo "  none"

# ── Regenerate the wire format from the QuackyDucky description ─────
# (Run after editing ymodem.qd.rfc; then `make verify` to refresh .checked.)
gen:
	@echo "Regenerating YModem.Wire.Generated.* from ymodem.qd.rfc ..."
	$(QD) -pulse -prefix "YModem.Wire.Generated." -odir $(SPEC_DIR) ymodem.qd.rfc
	@echo "Regenerated — now run 'make verify'."

# ═══════════════════════════════════════════════════════════════════
# Extraction to C
# ═══════════════════════════════════════════════════════════════════
# The executable *leaf* module to extract.  It is standalone (it uses only
# Pulse/F* array primitives), so Custard (--codegen C) emits one C file with
# unprefixed function names.  The verified runners (and the driver/dictionaries
# they use) are extracted separately by `extract-loops`.
IMPL_MODULES = YModem.Impl.Codec


$(EXTRACT_DIR):
	@mkdir -p $@

# ── F* → C ─────────────────────────────────────────────────────────
extract-c: verify | $(EXTRACT_DIR)
	@echo "Extracting YModem.Impl.Codec to C"
	@$(FSTAR) --codegen C --custard_monomorphize_types true \
	  --custard_entry_module YModem.Impl.Codec --custard_c_no_prefix YModem.Impl.Codec \
	  $(IMPL_DIR)/YModem.Impl.Codec.fst -o $(EXTRACT_DIR)/YModem_Impl_Codec.c
	@ls -lh $(EXTRACT_DIR)/YModem_Impl_Codec.c

extract: extract-c

# ── C wrappers (unverified interop drivers) ────────────────────────
# Compile the `rb`/`sb`-style interop wrappers against the extracted C.  Both
# wrappers link the single verified codec (emit/recv data block).
INTEROP_DIR  = interop
CC ?= gcc
CFLAGS_WRAP = -std=c11 -D_DEFAULT_SOURCE -Wall -Wextra \
  -I$(EXTRACT_DIR)

wrappers: extract-loops
	@echo "Compiling YMODEM interop drivers over the VERIFIED runners..."
	$(CC) $(CFLAGS_VLOOP) -o $(EXTRACT_DIR)/ymodem_rb \
	  $(INTEROP_DIR)/ymodem_rb.c \
	  $(EXTRACT_DIR)/YModem_Verified.c \
	  $(STUBS_DIR)/common_tcp_custard.c $(STUBS_DIR)/common_tcp_stubs.c
	$(CC) $(CFLAGS_VLOOP) -o $(EXTRACT_DIR)/ymodem_sb \
	  $(INTEROP_DIR)/ymodem_sb.c \
	  $(EXTRACT_DIR)/YModem_Verified.c \
	  $(STUBS_DIR)/common_tcp_custard.c $(STUBS_DIR)/common_tcp_stubs.c
	@echo "Interop drivers ymodem_rb / ymodem_sb (verified runners) compiled to $(EXTRACT_DIR)/."

# ── Verified runners → C + end-to-end test ─────────────────────────
# Extract the VERIFIED YMODEM runners (ymodem_client_receive / ymodem_server_send
# in YModem.Impl.{Client,Server}.Socket) — the shared
# Common.ProtocolDriver.drive_steps loop, which Custard specialises to the
# YMODEM protocol_implementation / protocol_endpoint instances — to a single
# self-contained C bundle (_extract/YModem_Verified.c), then link the socketpair
# test harness that runs a real file transfer through them (verified sender ->
# verified receiver) and checks the reconstructed bytes.  The TCP stub is the
# trusted realization of the verified read/write interface.
VERIFIED_DIR = verified
STUBS_DIR    = ../c_stubs
CFLAGS_VLOOP = -std=c11 -D_DEFAULT_SOURCE -DCOMMON_TCP_CUSTARD_FULL_DECLS \
  -include $(STUBS_DIR)/common_tcp_custard.h -Wall -Wno-unused-function \
  -Wno-unused-parameter -Wno-implicit-function-declaration \
  -I$(EXTRACT_DIR) -I$(STUBS_DIR)

extract-loops: verify
	@echo "Extracting the verified runners to C ..."
	@EVERPARSE_HOME=$(EVERPARSE_HOME) bash extract_loops.sh

vloop-test: extract-loops
	@echo "Building the verified-runner transfer test ..."
	$(CC) $(CFLAGS_VLOOP) -o $(EXTRACT_DIR)/vloop_test \
	  $(VERIFIED_DIR)/vloop_test.c \
	  $(EXTRACT_DIR)/YModem_Verified.c \
	  $(STUBS_DIR)/common_tcp_custard.c $(STUBS_DIR)/common_tcp_stubs.c
	@echo "─────────────────────────────────────────────────────────────────"
	@echo " Verified server runner  ->  verified client runner  (over a socketpair)"
	@echo "─────────────────────────────────────────────────────────────────"
	@$(EXTRACT_DIR)/vloop_test $(INTEROP_DIR)/dummy.txt

# ── Clean ──────────────────────────────────────────────────────────
clean:
	rm -rf $(CACHE_DIR) $(OUTPUT_DIR) $(EXTRACT_DIR)
	rm -f .depend
	@echo "Cleaned build artifacts"

help:
	@echo "YMODEM sample - Makefile targets:"
	@echo "  make verify        - Verify all YMODEM modules (default)"
	@echo "  make gen           - Regenerate YModem.Wire.Generated.* from ymodem.qd.rfc"
	@echo "  make check-admits  - List admits in impl/"
	@echo "  make extract-c     - Extract the codec leaf to C (into _extract/)"
	@echo "  make extract       - verify + extract-c"
	@echo "  make wrappers      - Compile the rb/sb interop wrappers"
	@echo "  make extract-loops - Extract the verified runners to C (_extract/YModem_Verified.c)"
	@echo "  make vloop-test    - Build + run the verified server->client transfer test"
	@echo "  make clean         - Remove build artifacts"
