/* Test-only stand-in for a host's certificate verifier (the role Chromium's
   verifier plays for the client engine), built on OpenSSL.  It is linked only
   into tests; the atlas library itself does not use OpenSSL. */

#include "openssl_host_auth.h"

#include <openssl/bio.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/pem.h>
#include <openssl/rsa.h>
#include <openssl/x509.h>
#include <openssl/x509_vfy.h>
#include <openssl/core_names.h>
#include <openssl/objects.h>

#include <limits.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

struct tls13_peer_identity_s {
  EVP_PKEY *leaf_public_key;
};

struct tls13_trust_store_s {
  X509_STORE *raw;
};

static X509 *read_single_cert_der(const uint8_t *der, size_t der_len) {
  if (der_len > LONG_MAX) {
    return NULL;
  }
  const unsigned char *p = der;
  X509 *cert = d2i_X509(NULL, &p, (long)der_len);
  if (cert != NULL && p != der + der_len) {
    X509_free(cert);
    return NULL;
  }
  return cert;
}

bool tls13_openssl_peer_copy_public_key_der(
    const tls13_peer_identity *peer,
    uint8_t *out,
    size_t out_capacity,
    size_t *out_len) {
  if (peer == NULL || peer->leaf_public_key == NULL || out == NULL ||
      out_len == NULL) {
    return false;
  }
  int encoded_len = i2d_PUBKEY(peer->leaf_public_key, NULL);
  if (encoded_len <= 0 || (size_t)encoded_len > out_capacity) {
    return false;
  }
  unsigned char *cursor = out;
  if (i2d_PUBKEY(peer->leaf_public_key, &cursor) != encoded_len) {
    return false;
  }
  *out_len = (size_t)encoded_len;
  return true;
}

static bool validate_leaf_cert(
    const char *hostname,
    const tls13_trust_store *trust_store,
    size_t validation_time_seconds,
    X509 *leaf,
    STACK_OF(X509) *untrusted,
    tls13_peer_identity **out_peer) {
  if (hostname == NULL || trust_store == NULL || trust_store->raw == NULL ||
      leaf == NULL || out_peer == NULL) {
    return false;
  }

  *out_peer = NULL;
  bool ok = false;
  X509_STORE_CTX *ctx = NULL;
  tls13_peer_identity *peer = NULL;

  ctx = X509_STORE_CTX_new();
  peer = calloc(1, sizeof *peer);
  if (ctx == NULL || peer == NULL) {
    goto done;
  }
  if (X509_STORE_CTX_init(ctx, trust_store->raw, leaf, untrusted) != 1) {
    goto done;
  }
  X509_VERIFY_PARAM *param = X509_STORE_CTX_get0_param(ctx);
  if (param == NULL ||
      (X509_VERIFY_PARAM_set1_ip_asc(param, hostname) != 1 &&
       X509_VERIFY_PARAM_set1_host(param, hostname, 0) != 1)) {
    goto done;
  }
  /* Always validate at the explicit time the verified model was given. */
  time_t validation_time = (time_t)validation_time_seconds;
  if (validation_time < (time_t)0 ||
      (size_t)validation_time != validation_time_seconds) {
    goto done;
  }
  X509_VERIFY_PARAM_set_time(param, validation_time);
  if (X509_verify_cert(ctx) != 1) {
    goto done;
  }
  peer->leaf_public_key = X509_get_pubkey(leaf);
  if (peer->leaf_public_key == NULL) {
    goto done;
  }
  *out_peer = peer;
  peer = NULL;
  ok = true;

done:
  tls13_openssl_peer_identity_free(peer);
  X509_STORE_CTX_free(ctx);
  return ok;
}

/* Builds a store from the certificates [next] yields.  `X509_V_FLAG_PARTIAL_CHAIN`
   lets a configured anchor that is not itself self-signed (an intermediate,
   say) terminate the chain, which is what "these certificates are trusted"
   means here. */
static tls13_trust_store *trust_store_from(
    X509 *(*next)(void *state), void *state) {
  X509_STORE *raw = X509_STORE_new();
  tls13_trust_store *trust_store = calloc(1u, sizeof *trust_store);
  if (raw == NULL || trust_store == NULL) {
    X509_STORE_free(raw);
    free(trust_store);
    return NULL;
  }

  size_t added = 0u;
  X509 *anchor = NULL;
  while ((anchor = next(state)) != NULL) {
    if (X509_STORE_add_cert(raw, anchor) == 1) {
      added++;
    }
    X509_free(anchor);
  }
  ERR_clear_error();

  X509_VERIFY_PARAM *store_param = X509_STORE_get0_param(raw);
  if (added == 0u || store_param == NULL ||
      X509_VERIFY_PARAM_set_flags(store_param, X509_V_FLAG_PARTIAL_CHAIN) != 1) {
    X509_STORE_free(raw);
    free(trust_store);
    return NULL;
  }

  trust_store->raw = raw;
  return trust_store;
}

typedef struct {
  const unsigned char *cursor;
  const unsigned char *end;
  bool failed;
} der_anchor_reader;

static X509 *next_der_anchor(void *state) {
  der_anchor_reader *reader = state;
  if (reader->failed || reader->cursor >= reader->end) {
    return NULL;
  }
  long remaining = (long)(reader->end - reader->cursor);
  X509 *anchor = d2i_X509(NULL, &reader->cursor, remaining);
  if (anchor == NULL) {
    reader->failed = true;
  }
  return anchor;
}

static X509 *next_pem_anchor(void *state) {
  return PEM_read_bio_X509((BIO *)state, NULL, NULL, NULL);
}

/* [trust_anchors_der] is a concatenation of DER certificates, the form of
   TLS13.X509.Spec.trust_store; any trailing bytes that do not parse reject the
   whole set. */
tls13_trust_store *tls13_openssl_trust_store_new(
    const uint8_t *trust_anchors_der,
    size_t trust_anchors_der_len) {
  if (trust_anchors_der == NULL || trust_anchors_der_len == 0u ||
      trust_anchors_der_len > LONG_MAX) {
    return NULL;
  }
  der_anchor_reader reader = {
    trust_anchors_der, trust_anchors_der + trust_anchors_der_len, false};
  tls13_trust_store *trust_store = trust_store_from(next_der_anchor, &reader);
  if (trust_store != NULL && reader.failed) {
    tls13_openssl_trust_store_free(trust_store);
    return NULL;
  }
  return trust_store;
}

static tls13_trust_store *trust_store_from_pem(
    const uint8_t *trust_anchor_pem,
    size_t trust_anchor_pem_len) {
  if (trust_anchor_pem == NULL || trust_anchor_pem_len == 0u ||
      trust_anchor_pem_len > INT_MAX) {
    return NULL;
  }
  BIO *bio = BIO_new_mem_buf(trust_anchor_pem, (int)trust_anchor_pem_len);
  if (bio == NULL) {
    return NULL;
  }
  tls13_trust_store *trust_store = trust_store_from(next_pem_anchor, bio);
  BIO_free(bio);
  return trust_store;
}

bool tls13_openssl_validate_leaf_der_with_store(
    const char *hostname,
    const tls13_trust_store *trust_store,
    size_t validation_time_seconds,
    const uint8_t *leaf_der,
    size_t leaf_der_len,
    tls13_peer_identity **out_peer) {
  if (hostname == NULL || trust_store == NULL || leaf_der == NULL ||
      out_peer == NULL || leaf_der_len > LONG_MAX) {
    return false;
  }

  X509 *leaf = read_single_cert_der(leaf_der, leaf_der_len);
  bool ok = validate_leaf_cert(
      hostname,
      trust_store,
      validation_time_seconds,
      leaf,
      NULL,
      out_peer);
  X509_free(leaf);
  return ok;
}

bool tls13_openssl_validate_leaf_der_with_store_and_chain(
    const char *hostname,
    const tls13_trust_store *trust_store,
    size_t validation_time_seconds,
    const uint8_t *leaf_der,
    size_t leaf_der_len,
    const uint8_t *chain_der,
    size_t chain_der_len,
    const size_t *chain_offsets,
    const size_t *chain_lens,
    size_t chain_count,
    tls13_peer_identity **out_peer) {
  if (hostname == NULL || trust_store == NULL || leaf_der == NULL ||
      out_peer == NULL || leaf_der_len > LONG_MAX) {
    return false;
  }

  STACK_OF(X509) *untrusted = NULL;
  if (chain_der != NULL && chain_offsets != NULL && chain_lens != NULL &&
      chain_count > 1u) {
    untrusted = sk_X509_new_null();
    if (untrusted == NULL) {
      return false;
    }
    /* Entry 0 is the leaf; it is supplied separately. */
    for (size_t i = 1u; i < chain_count; ++i) {
      size_t offset = chain_offsets[i];
      size_t length = chain_lens[i];
      if (length == 0u || offset > chain_der_len ||
          length > chain_der_len - offset) {
        continue;
      }
      X509 *cert = read_single_cert_der(chain_der + offset, length);
      if (cert == NULL) {
        continue;
      }
      if (sk_X509_push(untrusted, cert) <= 0) {
        X509_free(cert);
        sk_X509_pop_free(untrusted, X509_free);
        return false;
      }
    }
  }

  X509 *leaf = read_single_cert_der(leaf_der, leaf_der_len);
  bool ok = validate_leaf_cert(
      hostname,
      trust_store,
      validation_time_seconds,
      leaf,
      untrusted,
      out_peer);
  X509_free(leaf);
  sk_X509_pop_free(untrusted, X509_free);
  return ok;
}

bool tls13_openssl_validate_leaf_der(
    const char *hostname,
    const uint8_t *trust_anchor_pem,
    size_t trust_anchor_pem_len,
    const uint8_t *leaf_der,
    size_t leaf_der_len,
    tls13_peer_identity **out_peer) {
  if (hostname == NULL || trust_anchor_pem == NULL || leaf_der == NULL || out_peer == NULL ||
      trust_anchor_pem_len > INT_MAX || leaf_der_len > LONG_MAX) {
    return false;
  }

  tls13_trust_store *trust_store =
      trust_store_from_pem(trust_anchor_pem, trust_anchor_pem_len);
  time_t now = time(NULL);
  bool ok = now > (time_t)0 &&
      tls13_openssl_validate_leaf_der_with_store(
          hostname, trust_store, (size_t)now, leaf_der, leaf_der_len, out_peer);
  tls13_openssl_trust_store_free(trust_store);
  return ok;
}

static bool verify_rsa_pss_rsae_sha256(
    EVP_PKEY *public_key,
    const uint8_t *message,
    size_t message_len,
    const uint8_t *signature,
    size_t signature_len) {
  if (public_key == NULL || EVP_PKEY_base_id(public_key) != EVP_PKEY_RSA) {
    return false;
  }

  bool ok = false;
  EVP_MD_CTX *ctx = EVP_MD_CTX_new();
  EVP_PKEY_CTX *pkey_ctx = NULL;
  if (ctx == NULL ||
      EVP_DigestVerifyInit(ctx, &pkey_ctx, EVP_sha256(), NULL, public_key) != 1 ||
      pkey_ctx == NULL ||
      EVP_PKEY_CTX_set_rsa_padding(pkey_ctx, RSA_PKCS1_PSS_PADDING) != 1 ||
      EVP_PKEY_CTX_set_rsa_pss_saltlen(pkey_ctx, RSA_PSS_SALTLEN_DIGEST) != 1 ||
      EVP_PKEY_CTX_set_rsa_mgf1_md(pkey_ctx, EVP_sha256()) != 1) {
    goto done;
  }
  ok = EVP_DigestVerify(ctx, signature, signature_len, message, message_len) == 1;

done:
  EVP_MD_CTX_free(ctx);
  return ok;
}

/* TLS 1.3 ecdsa_secp256r1_sha256: SHA-256 over the message, verified against a
   P-256 key, with the signature in the DER SEQUENCE{r,s} form that TLS 1.3
   mandates -- exactly what EVP_DigestVerify consumes, so no re-encoding. */
static bool verify_ecdsa_secp256r1_sha256(
    EVP_PKEY *public_key,
    const uint8_t *message,
    size_t message_len,
    const uint8_t *signature,
    size_t signature_len) {
  if (public_key == NULL || EVP_PKEY_base_id(public_key) != EVP_PKEY_EC) {
    return false;
  }

  char group[64];
  size_t group_len = 0u;
  if (EVP_PKEY_get_utf8_string_param(
          public_key, OSSL_PKEY_PARAM_GROUP_NAME, group, sizeof group,
          &group_len) != 1 ||
      strcmp(group, SN_X9_62_prime256v1) != 0) {
    return false;
  }

  bool ok = false;
  EVP_MD_CTX *ctx = EVP_MD_CTX_new();
  if (ctx == NULL ||
      EVP_DigestVerifyInit(ctx, NULL, EVP_sha256(), NULL, public_key) != 1) {
    goto done;
  }
  ok = EVP_DigestVerify(ctx, signature, signature_len, message, message_len) == 1;

done:
  EVP_MD_CTX_free(ctx);
  return ok;
}

bool tls13_openssl_peer_verify_signature(
    const tls13_peer_identity *peer,
    uint16_t signature_scheme,
    const uint8_t *message,
    size_t message_len,
    const uint8_t *signature,
    size_t signature_len) {
  if (peer == NULL || message == NULL || signature == NULL) {
    return false;
  }
  switch (signature_scheme) {
  case TLS13_SIG_RSA_PSS_RSAE_SHA256:
    return verify_rsa_pss_rsae_sha256(
        peer->leaf_public_key, message, message_len, signature, signature_len);
  case TLS13_SIG_ECDSA_SECP256R1_SHA256:
    return verify_ecdsa_secp256r1_sha256(
        peer->leaf_public_key, message, message_len, signature, signature_len);
  default:
    return false;
  }
}

void tls13_openssl_peer_identity_free(tls13_peer_identity *peer) {
  if (peer == NULL) {
    return;
  }
  EVP_PKEY_free(peer->leaf_public_key);
  free(peer);
}

void tls13_openssl_trust_store_free(tls13_trust_store *trust_store) {
  if (trust_store == NULL) {
    return;
  }
  X509_STORE_free(trust_store->raw);
  free(trust_store);
}

