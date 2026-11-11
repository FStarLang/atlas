all: depend verify

EVERPARSE_HOME ?= $(realpath $(CURDIR)/../../everparse)
EVERPARSE_LIB_PATH ?= $(EVERPARSE_HOME)/lib/everparse

LOWPARSE_HOME ?= $(EVERPARSE_LIB_PATH)/lowparse

ifdef NO_QD_VERIFY
LAX_EXT=.lax
LAX_OPT=--lax
else
LAX_EXT=
LAX_OPT=
endif

ASN1_HOME ?= $(EVERPARSE_LIB_PATH)/asn1

INCLUDE_PATHS += $(LOWPARSE_HOME) $(ASN1_HOME)/spec $(ASN1_HOME)/pulse ..
ALREADY_CACHED := C,Spec.Loops,LowParse,ASN1,
CACHE_DIRECTORY := cache$(LAX_EXT)
OUTPUT_DIRECTORY := krml
FSTAR_DEP_FILE := .depend$(LAX_EXT)
FSTAR_FILES := $(wildcard *.fst *.fsti)
FSTAR_DEP_OPTIONS :=

clean_rules += clean-local

include $(EVERPARSE_LIB_PATH)/common.Makefile

# --warn_error +241: the F* toolchain install may ship Pulse .checked files whose
# dependence hashes don't match under these harness flags; downgrade the "stale
# checked, will recheck" error (241) to a warning so F* transparently rechecks
# them (otherwise a cold-cache run — e.g. a fresh checkout — aborts).
FSTAR_OPTIONS += $(LAX_OPT) --warn_error @272 --warn_error +241

export LOWPARSE_HOME

HEADERS = $(addprefix -add-include ,'"krml/internal/compat.h"')

ifeq ($(OS),Darwin)
KRML_OPTS += -ccopt -Wno-tautological-constant-out-of-range-compare
endif

# -Wno-tautological-overlap-compare because of T32
# KRML_WARN: Warning 9/17 (globals needing krmlinit_globals) stay fatal: the
# QuackyDucky enum lookup tables are emitted `noextract` (inlined at use sites),
# so the generated parsers/serializers no longer require krmlinit_globals().
KRML_WARN ?= @2-26
KRML = $(KRML_EXE) \
	 -fstar $(FSTAR_EXE) \
	 -ccopt "-O3" -ccopt "-ffast-math" \
	 -ccopt "-Wno-tautological-overlap-compare" \
	 -drop 'FStar.Tactics.\*' -drop FStar.Tactics -drop 'FStar.Reflection.\*' \
	 -tmpdir out -I .. \
	 -bundle 'LowParse.\*' \
	 $(KRML_OPTS) \
	 $(HEADERS) \
	 -warn-error '$(KRML_WARN)'

# Custard (F*'s whole-program extractor) emits one KaRaMeL JSON file holding
# every generated wire module; every top-level definition is an extraction root.
# The X.509 modules are left out: atlas extracts by reachability, and their
# writers, which atlas never calls, are most of their code.
CUSTARD_BACKEND := KrmlC
CUSTARD_ENTRY_MODULES := $(filter-out TLS13.Wire.Generated.X509%,\
  $(basename $(wildcard TLS13.Wire.Generated.*.fst)))
CUSTARD_ROOTS := TLS13.Wire.Generated.Handshake.fst

extract: $(CUSTARD_KRML)
	-@mkdir out
	$(KRML) -skip-compilation $<

depend: $(FSTAR_DEP_FILE)

clean-local:
	-rm -rf out cache cache.lax .depend .depend.lax krml

.PHONY: all depend extract clean-local
