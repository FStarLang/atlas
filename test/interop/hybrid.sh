#!/usr/bin/env bash
# X25519MLKEM768 (RFC 10024) interop between the verified endpoints and
# OpenSSL 3.5, run by `make test-hybrid-interop`.
#
# Verified client: the OpenSSL server is pinned to `-groups X25519MLKEM768`.
# The verified client does not implement HelloRetryRequest, so a completed
# handshake shows that it sent a hybrid key share and that the hybrid was used.
#
# Verified server: the OpenSSL client sends both an X25519MLKEM768 and an
# X25519 key share (the shape of OpenSSL 3.5's, Chrome's and Firefox's
# default offer), and the test checks that the server chose the hybrid.  The
# server picks the hybrid only next to an X25519 share; a ClientHello whose
# only share is the hybrid is refused, because there is no HelloRetryRequest.
#
# The system OpenSSL (3.0) has no ML-KEM.  The test needs the OpenSSL 3.5 CLI
# from scripts/build-openssl35.sh and is skipped, not failed, when it is absent.
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$repo_root"
openssl35="${OPENSSL35:-$repo_root/tools/openssl-3.5/bin/openssl}"

if [ ! -x "$openssl35" ]; then
  echo "hybrid interop: SKIPPED (no OpenSSL 3.5 at $openssl35; run scripts/build-openssl35.sh)"
  exit 0
fi

free_port() {
  python3 -c 'import socket; s=socket.socket(); s.bind(("127.0.0.1",0)); print(s.getsockname()[1]); s.close()'
}

work="$(mktemp -d)"
pids=()
cleanup() {
  for p in "${pids[@]}"; do kill "$p" 2>/dev/null || true; done
  rm -rf "$work"
}
trap cleanup EXIT

# Verified client -> OpenSSL 3.5 server.
port="$(free_port)"
"$openssl35" s_server -accept "127.0.0.1:$port" -naccept 1 -www -tls1_3 \
  -groups X25519MLKEM768 \
  -cert test/certs/chain.pem -key test/certs/leaf.key \
  > "$work/s_server.log" 2>&1 &
pids+=($!)
result=""
for _ in $(seq 1 50); do
  result="$(./test/test_interop_client localhost test/certs/ca.pem "$port" 2>&1 || true)"
  case "$result" in *"RESULT"*"TCP"*) sleep 0.1 ;; *) break ;; esac
done
case "$result" in
  *"RESULT"*"OK"*"200"*)
    echo "hybrid interop: verified client -> OpenSSL 3.5 server (X25519MLKEM768) passed" ;;
  *)
    echo "hybrid interop: verified client -> OpenSSL 3.5 server FAILED"
    echo "$result"; cat "$work/s_server.log"; exit 1 ;;
esac

# OpenSSL 3.5 client -> verified server.
port="$(free_port)"
./test/test_hybrid_server_peer "$port" test/certs/leaf.der test/certs/leaf.key \
  > "$work/server.log" 2>&1 &
server_pid=$!
pids+=($server_pid)
out=""
for _ in $(seq 1 50); do
  out="$( (printf 'ping-hybrid\n'; sleep 1) | "$openssl35" s_client \
      -connect "127.0.0.1:$port" -servername localhost -tls1_3 \
      -groups '*X25519MLKEM768:*X25519' -CAfile test/certs/ca.pem -verify_return_error \
      -ign_eof 2>&1 || true)"
  case "$out" in *"Connection refused"*|*"connect:errno"*) sleep 0.1 ;; *) break ;; esac
done
if ! wait "$server_pid"; then
  echo "hybrid interop: OpenSSL 3.5 client -> verified server FAILED"
  cat "$work/server.log"; echo "$out"; exit 1
fi
case "$out" in
  *"Negotiated TLS1.3 group: X25519MLKEM768"*"ping-hybrid"*)
    echo "hybrid interop: OpenSSL 3.5 client -> verified server (X25519MLKEM768) passed" ;;
  *)
    echo "hybrid interop: OpenSSL 3.5 client -> verified server FAILED"
    echo "$out"; exit 1 ;;
esac
