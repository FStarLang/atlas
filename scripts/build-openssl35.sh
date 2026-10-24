#!/usr/bin/env bash
# Optional: build OpenSSL 3.5 (the first release with ML-KEM and the
# X25519MLKEM768 TLS group of RFC 10024) into tools/openssl-3.5.
#
# Only its `openssl` command-line tool is used, as the peer in the
# X25519MLKEM768 interop tests (`make test-hybrid-interop`).  Nothing links
# against it, and the tests skip, rather than fail, when it is absent.
set -euo pipefail

version="${OPENSSL35_VERSION:-3.5.4}"
repo_root="$(cd "$(dirname "$0")/.." && pwd)"
prefix="$repo_root/tools/openssl-3.5"

if [ -x "$prefix/bin/openssl" ]; then
  "$prefix/bin/openssl" version
  exit 0
fi

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
cd "$work"
curl -fsSL -o openssl.tar.gz \
  "https://github.com/openssl/openssl/releases/download/openssl-$version/openssl-$version.tar.gz"
tar xzf openssl.tar.gz
cd "openssl-$version"
./Configure --prefix="$prefix" --openssldir="$prefix/ssl" --libdir=lib \
  no-docs no-tests no-shared >/dev/null
make -j"$(nproc)" >/dev/null
make install_sw >/dev/null
"$prefix/bin/openssl" version
