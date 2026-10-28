#!/usr/bin/env bash
# Extract the verified TFTP runners (the shared Common.ProtocolDriver loop
# specialised to the TFTP endpoints, + their deps) to a single C bundle,
# mirroring ymodem_sample/extract_loops.sh.  The runners tftp_client_receive /
# tftp_server_send lower to first-order C in _extract/TFTP_Verified.c — the
# runnable verified orchestration the vloop_test harness and the interop
# programs link against.
set -e
EP=${EVERPARSE_HOME:-/workspaces/atlas/tools/everparse}
FS=$EP/opt/FStar/bin/fstar.exe
LP=$EP/lib/everparse/lowparse
export PATH=$EP/opt/z3:$PATH
cd "$(dirname "$0")"
F="--cache_checked_modules --cache_dir _cache --odir _output --already_cached Prims,FStar,Pulse,PulseCore,C,Spec.Loops,LowParse --warn_error -321-241-272-288 --report_assumes warn --ext optimize_let_vc --ext fly_deps --include ../common --include $LP --include spec --include impl"

MODS="TFTP.Impl.Codec TFTP.Impl.Client.Socket TFTP.Impl.Server.Socket"

# Custard (F*'s whole-program extractor) extracts, from the checked files, the
# functions the C drivers in verified/ and interop/ call and everything they
# reach, straight to one C file (--codegen C).
# Extraction is by reachability, so these roots are the whole C surface.  Custard
# takes a single file on the command line and loads the other modules on demand.
ENTRIES=""
for E in \
  TFTP.Impl.Client.Socket.tftp_client_receive \
  TFTP.Impl.Server.Socket.tftp_server_send \
  ; do ENTRIES="$ENTRIES --custard_entry $E"; done
EXTERN_TYPES="--custard_extern_type Common.TCP.channel@common_tcp_custard.h --custard_extern_type Common.TCP.listener@common_tcp_custard.h"
# The C drivers call the roots by their unqualified names.
NO_PREFIX=""
for M in TFTP.Impl.Client.Socket TFTP.Impl.Server.Socket; do NO_PREFIX="$NO_PREFIX --custard_c_no_prefix $M"; done
set -- $MODS
SRC=impl/$1.fst
rm -rf _extract
mkdir -p _extract
$FS $F --codegen C --custard_monomorphize_types true $ENTRIES $NO_PREFIX $EXTERN_TYPES $SRC -o _extract/TFTP_Verified.c >/dev/null
echo "=== generated ==="
ls -1 _extract/*.c _extract/*.h 2>/dev/null
