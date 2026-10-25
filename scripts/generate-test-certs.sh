#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
dest_dir="${1:-"$repo_root/test/certs"}"

mkdir -p "$dest_dir"

openssl req -x509 -newkey rsa:2048 -nodes -days 30 \
  -subj "/CN=atlas test CA" \
  -keyout "$dest_dir/ca.key" \
  -out "$dest_dir/ca.pem" \
  >/dev/null 2>&1

cat > "$dest_dir/leaf.ext" <<'EOF'
basicConstraints = CA:FALSE
keyUsage = digitalSignature, keyEncipherment
extendedKeyUsage = serverAuth
subjectAltName = DNS:localhost,IP:127.0.0.1
EOF

openssl req -newkey rsa:2048 -nodes \
  -subj "/CN=localhost" \
  -keyout "$dest_dir/leaf.key" \
  -out "$dest_dir/leaf.csr" \
  >/dev/null 2>&1

openssl x509 -req -days 30 \
  -in "$dest_dir/leaf.csr" \
  -CA "$dest_dir/ca.pem" \
  -CAkey "$dest_dir/ca.key" \
  -CAcreateserial \
  -extfile "$dest_dir/leaf.ext" \
  -out "$dest_dir/leaf.pem" \
  >/dev/null 2>&1

openssl x509 -in "$dest_dir/leaf.pem" -outform DER -out "$dest_dir/leaf.der" >/dev/null 2>&1

cat "$dest_dir/leaf.pem" > "$dest_dir/chain.pem"

# Parity gap G5: an ECDSA P-256 leaf, issued by the same test CA, so the
# verified server can be exercised with a non-RSA credential.
openssl req -newkey ec -pkeyopt ec_paramgen_curve:prime256v1 -nodes \
  -subj "/CN=localhost" \
  -keyout "$dest_dir/ec-leaf.key" \
  -out "$dest_dir/ec-leaf.csr" \
  >/dev/null 2>&1

openssl x509 -req -days 30 \
  -in "$dest_dir/ec-leaf.csr" \
  -CA "$dest_dir/ca.pem" \
  -CAkey "$dest_dir/ca.key" \
  -CAcreateserial \
  -extfile "$dest_dir/leaf.ext" \
  -out "$dest_dir/ec-leaf.pem" \
  >/dev/null 2>&1

openssl x509 -in "$dest_dir/ec-leaf.pem" -outform DER \
  -out "$dest_dir/ec-leaf.der" >/dev/null 2>&1

cat "$dest_dir/ec-leaf.pem" > "$dest_dir/ec-chain.pem"

# A P-256 intermediate CA under the test CA, and an RSA leaf it issues: the
# server sends both, so the client must build the path through the
# intermediate to reach its configured anchor.
cat > "$dest_dir/inter.ext" <<'EOF'
basicConstraints = critical, CA:TRUE, pathlen:0
keyUsage = critical, keyCertSign
EOF

openssl req -newkey ec -pkeyopt ec_paramgen_curve:prime256v1 -nodes \
  -subj "/CN=atlas test intermediate" \
  -keyout "$dest_dir/inter.key" \
  -out "$dest_dir/inter.csr" \
  >/dev/null 2>&1

openssl x509 -req -days 30 \
  -in "$dest_dir/inter.csr" \
  -CA "$dest_dir/ca.pem" \
  -CAkey "$dest_dir/ca.key" \
  -CAcreateserial \
  -extfile "$dest_dir/inter.ext" \
  -out "$dest_dir/inter.pem" \
  >/dev/null 2>&1

openssl req -newkey rsa:2048 -nodes \
  -subj "/CN=localhost" \
  -keyout "$dest_dir/inter-leaf.key" \
  -out "$dest_dir/inter-leaf.csr" \
  >/dev/null 2>&1

openssl x509 -req -days 30 \
  -in "$dest_dir/inter-leaf.csr" \
  -CA "$dest_dir/inter.pem" \
  -CAkey "$dest_dir/inter.key" \
  -CAcreateserial \
  -extfile "$dest_dir/leaf.ext" \
  -out "$dest_dir/inter-leaf.pem" \
  >/dev/null 2>&1

cat "$dest_dir/inter-leaf.pem" "$dest_dir/inter.pem" > "$dest_dir/inter-chain.pem"

# An all-ECDSA-SHA384 path in the shape of public ECC hierarchies: a P-384
# root, a P-384 intermediate it signs, a P-256 intermediate signed by that,
# and a P-256 leaf.  Every signature is ecdsa-with-SHA384, so the path
# exercises P-384/SHA-384 and P-256/SHA-384 verification.
openssl req -x509 -newkey ec -pkeyopt ec_paramgen_curve:secp384r1 -nodes \
  -sha384 -days 30 \
  -subj "/CN=atlas test ECC root" \
  -keyout "$dest_dir/ecc-ca.key" \
  -out "$dest_dir/ecc-ca.pem" \
  >/dev/null 2>&1

cat > "$dest_dir/ecc-inter384.ext" <<'EOF'
basicConstraints = critical, CA:TRUE, pathlen:1
keyUsage = critical, keyCertSign
EOF

openssl req -newkey ec -pkeyopt ec_paramgen_curve:secp384r1 -nodes \
  -subj "/CN=atlas test P-384 intermediate" \
  -keyout "$dest_dir/ecc-inter384.key" \
  -out "$dest_dir/ecc-inter384.csr" \
  >/dev/null 2>&1

openssl x509 -req -days 30 -sha384 \
  -in "$dest_dir/ecc-inter384.csr" \
  -CA "$dest_dir/ecc-ca.pem" \
  -CAkey "$dest_dir/ecc-ca.key" \
  -CAcreateserial \
  -extfile "$dest_dir/ecc-inter384.ext" \
  -out "$dest_dir/ecc-inter384.pem" \
  >/dev/null 2>&1

openssl req -newkey ec -pkeyopt ec_paramgen_curve:prime256v1 -nodes \
  -subj "/CN=atlas test P-256 intermediate" \
  -keyout "$dest_dir/ecc-inter256.key" \
  -out "$dest_dir/ecc-inter256.csr" \
  >/dev/null 2>&1

openssl x509 -req -days 30 -sha384 \
  -in "$dest_dir/ecc-inter256.csr" \
  -CA "$dest_dir/ecc-inter384.pem" \
  -CAkey "$dest_dir/ecc-inter384.key" \
  -CAcreateserial \
  -extfile "$dest_dir/inter.ext" \
  -out "$dest_dir/ecc-inter256.pem" \
  >/dev/null 2>&1

openssl req -newkey ec -pkeyopt ec_paramgen_curve:prime256v1 -nodes \
  -subj "/CN=localhost" \
  -keyout "$dest_dir/ecc-leaf.key" \
  -out "$dest_dir/ecc-leaf.csr" \
  >/dev/null 2>&1

openssl x509 -req -days 30 -sha384 \
  -in "$dest_dir/ecc-leaf.csr" \
  -CA "$dest_dir/ecc-inter256.pem" \
  -CAkey "$dest_dir/ecc-inter256.key" \
  -CAcreateserial \
  -extfile "$dest_dir/leaf.ext" \
  -out "$dest_dir/ecc-leaf.pem" \
  >/dev/null 2>&1

cat "$dest_dir/ecc-leaf.pem" "$dest_dir/ecc-inter256.pem" "$dest_dir/ecc-inter384.pem" \
  > "$dest_dir/ecc-chain.pem"

# A P-384 leaf under the P-384 intermediate: its TLS CertificateVerify is
# ecdsa_secp384r1_sha384.
openssl req -newkey ec -pkeyopt ec_paramgen_curve:secp384r1 -nodes \
  -subj "/CN=localhost" \
  -keyout "$dest_dir/ecc384-leaf.key" \
  -out "$dest_dir/ecc384-leaf.csr" \
  >/dev/null 2>&1

openssl x509 -req -days 30 -sha384 \
  -in "$dest_dir/ecc384-leaf.csr" \
  -CA "$dest_dir/ecc-inter384.pem" \
  -CAkey "$dest_dir/ecc-inter384.key" \
  -CAcreateserial \
  -extfile "$dest_dir/leaf.ext" \
  -out "$dest_dir/ecc384-leaf.pem" \
  >/dev/null 2>&1

cat "$dest_dir/ecc384-leaf.pem" "$dest_dir/ecc-inter384.pem" \
  > "$dest_dir/ecc384-chain.pem"

echo "Generated test certificates in $dest_dir"
