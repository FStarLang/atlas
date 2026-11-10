#!/usr/bin/env bash
# Clone and build EverParse (QuackyDucky + LowParse + the ASN.1 library + the
# F*/KaRaMeL toolchain it vendors under opt/FStar) from the fork/branch used by
# this project.
#
# `make quackyducky asn1` in the EverParse tree builds everything we need:
#   - the F* binary           at opt/FStar/out/bin/fstar.exe (symlinked opt/FStar/bin/fstar.exe)
#   - the KaRaMeL binary       at opt/FStar/karamel/out/bin/krml (F*'s karamel submodule)
#   - the QuackyDucky compiler at bin/everparse-qd.exe
#   - the verified LowParse + LowParse.Pulse .checked libraries under lib/everparse/lowparse
#   - the everparse-asn1 compiler at bin/everparse-asn1.exe, and the verified
#     ASN.1 DER spec + Pulse library .checked files under lib/everparse/asn1
#
# The atlas Makefile consumes this toolchain via EVERPARSE_HOME (no separate
# F* install is required).
set -euo pipefail

EVERPARSE_REPO="${EVERPARSE_REPO:-https://github.com/project-everest/everparse}"
EVERPARSE_BRANCH="${EVERPARSE_BRANCH:-master}"
# Pinned EverParse commit this project is verified against.  The branch above is
# only used as a fetch hint; the build always checks out this exact commit so the
# toolchain is reproducible regardless of where the branch tip has moved.
EVERPARSE_COMMIT="${EVERPARSE_COMMIT:-72608ae1af92ab6ae9a84fb45c82a4b6397d5562}"
# F* revision to build EverParse with, overriding the FStar_hash EverParse pins
# in opt/hashes.Makefile.  This is the commit of the F* nightly that hacl-pulse
# (scripts/build-hacl-pulse.sh) is verified against (its .fstar-nightly), so
# both are built with the same F*.  KaRaMeL is F*'s karamel submodule.
FSTAR_COMMIT="${FSTAR_COMMIT:-157c3114336cd616bd34a49a9f0d4fef1b64cd9b}"

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# Default location: tools/everparse inside the atlas checkout (matches the
# Makefile's EVERPARSE_HOME default of $(CURDIR)/tools/everparse, and the
# tools/FStar convention used previously).  Override with EVERPARSE_HOME.
EVERPARSE_HOME="${EVERPARSE_HOME:-$repo_root/tools/everparse}"
jobs="${JOBS:-$(nproc 2>/dev/null || echo 4)}"

fstar_exe="$EVERPARSE_HOME/opt/FStar/out/bin/fstar.exe"
krml_exe="$EVERPARSE_HOME/opt/FStar/karamel/out/bin/krml"
qd_exe="$EVERPARSE_HOME/bin/everparse-qd.exe"
asn1_exe="$EVERPARSE_HOME/bin/everparse-asn1.exe"

for cmd in git make opam; do
  if ! command -v "$cmd" >/dev/null 2>&1; then
    echo "missing prerequisite: $cmd" >&2
    exit 1
  fi
done

if [ -d "$EVERPARSE_HOME/.git" ] &&
   [ -x "$fstar_exe" ] && [ -x "$krml_exe" ] && [ -x "$qd_exe" ] && [ -x "$asn1_exe" ] &&
   [ "$(git -C "$EVERPARSE_HOME" rev-parse HEAD)" = "$EVERPARSE_COMMIT" ] &&
   [ "$(git -C "$EVERPARSE_HOME/opt/FStar" rev-parse HEAD 2>/dev/null)" = "$FSTAR_COMMIT" ]; then
  echo "EverParse toolchain already built at $EVERPARSE_COMMIT (F* $FSTAR_COMMIT) in $EVERPARSE_HOME"
  exit 0
fi

if [ ! -d "$EVERPARSE_HOME/.git" ]; then
  echo "Cloning EverParse ($EVERPARSE_REPO @ $EVERPARSE_BRANCH) into $EVERPARSE_HOME ..."
  mkdir -p "$(dirname "$EVERPARSE_HOME")"
  git clone --branch "$EVERPARSE_BRANCH" "$EVERPARSE_REPO" "$EVERPARSE_HOME"
else
  echo "Updating existing EverParse checkout in $EVERPARSE_HOME ..."
  # An older checkout may point at a different fork; re-point it at
  # $EVERPARSE_REPO so the pinned commit below is actually fetchable.
  git -C "$EVERPARSE_HOME" remote set-url origin "$EVERPARSE_REPO"
  git -C "$EVERPARSE_HOME" fetch origin "$EVERPARSE_BRANCH"
fi

echo "Checking out pinned EverParse commit $EVERPARSE_COMMIT ..."
# Drop the FStar_hash override written by a previous run before switching.
git -C "$EVERPARSE_HOME" checkout --quiet -- opt/hashes.Makefile
git -C "$EVERPARSE_HOME" checkout --quiet "$EVERPARSE_COMMIT"

# Point EverParse's opt/Makefile at $FSTAR_COMMIT.  Rewriting hashes.Makefile
# also makes it newer than opt/FStar/Makefile, so the opt/ rules re-fetch and
# check out the new F* revision in an existing opt/FStar clone.
sed -i "s/^FStar_hash *:=.*/FStar_hash := $FSTAR_COMMIT/" \
  "$EVERPARSE_HOME/opt/hashes.Makefile"

# When the F* revision moves, build artifacts left over from the previous one
# (stale .checked files in particular) make the build fail, so wipe the
# ignored/untracked files of the F* checkout and its karamel submodule.
fstar_dir="$EVERPARSE_HOME/opt/FStar"
if [ -d "$fstar_dir/.git" ] &&
   [ "$(git -C "$fstar_dir" rev-parse HEAD)" != "$FSTAR_COMMIT" ]; then
  echo "Pinned F* revision changed; cleaning stale build artifacts in $fstar_dir ..."
  git -C "$fstar_dir" clean -xfdq
  if [ -e "$fstar_dir/karamel/.git" ]; then
    git -C "$fstar_dir/karamel" clean -xfdq
  fi
  rm -f "$EVERPARSE_HOME/opt/FStar.done" "$EVERPARSE_HOME/opt/karamel.done"
fi

echo "Building EverParse (make quackyducky asn1 -j$jobs) — this also builds F* and KaRaMeL ..."
make -C "$EVERPARSE_HOME" -j"$jobs" deps
ADMIT=1 make -C "$EVERPARSE_HOME" -j"$jobs" quackyducky asn1

for f in "$fstar_exe" "$krml_exe" "$qd_exe" "$asn1_exe"; do
  if [ ! -x "$f" ]; then
    echo "EverParse build did not produce $f" >&2
    exit 1
  fi
done

echo "EverParse toolchain ready in $EVERPARSE_HOME"
echo "  F*:          $fstar_exe"
echo "  KaRaMeL:     $krml_exe"
echo "  QuackyDucky: $qd_exe"
echo "  ASN.1:       $asn1_exe"
