#!/usr/bin/env bash
# Run the ATLAS interop harness against every host in a catalog.
#
#   usage: test/interop/sweep.sh [catalog.tsv] [out.tsv] [parallelism]
#
# Requires `make interop-client` to have built test/test_interop_client, and
# outbound network access on port 443.  Every host is validated against the
# system trust store (SSL_CERT_FILE, else the distribution bundle), as a
# deployed client would.
set -u

REPO=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
CAT="${1:-$REPO/test/interop/top100.tsv}"
OUT="${2:-$REPO/test/interop/sweep.tsv}"
PAR="${3:-12}"

export HARNESS="$REPO/test/test_interop_client"

if [ ! -x "$HARNESS" ]; then
  echo "missing $HARNESS -- run 'make interop-client' first" >&2
  exit 1
fi

run_one() {
  local rank="$1" host="$2" connect_host="$3"
  local line
  line=$(timeout 30 "$HARNESS" "$connect_host" - 443 2>/dev/null \
           | grep '^RESULT' | head -1)
  if [ -z "$line" ]; then
    printf '%s\t%s\t%s\tCRASH\tno RESULT line\n' "$rank" "$host" "$connect_host"
    return
  fi
  printf '%s\t%s\t%s\t%s\t%s\n' "$rank" "$host" "$connect_host" \
    "$(printf '%s' "$line" | cut -f3)" "$(printf '%s' "$line" | cut -f4)"
}
export -f run_one

grep -v '^#' "$CAT" | tr -d '\r' | \
  xargs -P "$PAR" -L1 bash -c 'run_one "$@"' _ > "$OUT"
sort -n -k1,1 -o "$OUT" "$OUT"
echo "wrote $OUT"
cut -f4 "$OUT" | sort | uniq -c | sort -rn
