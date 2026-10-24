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
# The peer is the system OpenSSL (>= 3.5, the first release with ML-KEM);
# set OPENSSL to use another binary.
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$repo_root"
openssl_bin="${OPENSSL:-openssl}"

if ! "$openssl_bin" list -kem-algorithms 2>/dev/null | grep -qi 'ML-KEM-768'; then
  echo "hybrid interop: FAILED ($openssl_bin has no ML-KEM-768; OpenSSL >= 3.5 is required)"
  "$openssl_bin" version 2>&1 || true
  exit 1
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
"$openssl_bin" s_server -accept "127.0.0.1:$port" -naccept 1 -www -tls1_3 \
  -groups X25519MLKEM768 \
  -cert test/certs/chain.pem -key test/certs/leaf.key \
  > "$work/s_server.log" 2>&1 &
pids+=($!)
# Wait for s_server to listen.  A probe connection would use up -naccept 1,
# and the client reports a refused connection as a handshake failure, so poll
# for s_server's ACCEPT line instead.
for _ in $(seq 1 100); do
  grep -q '^ACCEPT' "$work/s_server.log" && break
  sleep 0.1
done
result="$(./test/test_interop_client localhost test/certs/ca.pem "$port" 2>&1 || true)"
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
  out="$( (printf 'ping-hybrid\n'; sleep 1) | "$openssl_bin" s_client \
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
