#include "tls13_openssl_custard.h"

#include "custard_option.h"

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

CUSTARD_OPTION_TYPE(option_size, size_t);
CUSTARD_OPTION_TYPE(option_server_credentials, TLS13_OpenSSL_server_credentials);

#include "tls13_openssl_stubs.h"

#include <stdatomic.h>
#include <stdlib.h>
#include <string.h>

/* Certificate validation is done by the verified validator
   (TLS13.Impl.X509.Validate) from the connection's own configuration, so the
   auth config and context no longer carry validation state; they remain as
   reference-counted handles only. */
struct TLS13_OpenSSL_auth_config_s {
  atomic_size_t references;
};

struct TLS13_OpenSSL_auth_context_s {
  TLS13_OpenSSL_auth_config config;
};

struct TLS13_OpenSSL_server_credentials_s {
  atomic_size_t references;
  tls13_server_credentials *raw;
};

void TLS13_OpenSSL_auth_config_free(TLS13_OpenSSL_auth_config config);
void TLS13_OpenSSL_auth_context_free(TLS13_OpenSSL_auth_context ctx);
void TLS13_OpenSSL_server_credentials_free(TLS13_OpenSSL_server_credentials creds);

static void auth_config_retain(TLS13_OpenSSL_auth_config config) {
  (void)atomic_fetch_add_explicit(
      &config->references, (size_t)1u, memory_order_relaxed);
}

TLS13_OpenSSL_auth_config
TLS13_OpenSSL_auth_config_new(
    uint8_t *server_name,
    size_t server_name_len,
    uint8_t *trust_anchors,
    size_t trust_anchors_len,
    size_t validation_time_seconds) {
  TLS13_OpenSSL_auth_config config = calloc(1u, sizeof *config);
  if (config == NULL) {
    abort();
  }
  (void)server_name;
  (void)server_name_len;
  (void)trust_anchors;
  (void)trust_anchors_len;
  (void)validation_time_seconds;
  atomic_init(&config->references, (size_t)1u);
  return config;
}

TLS13_OpenSSL_auth_context
TLS13_OpenSSL_auth_context_new(TLS13_OpenSSL_auth_config config) {
  if (config == NULL) {
    abort();
  }
  TLS13_OpenSSL_auth_context ctx = calloc(1u, sizeof *ctx);
  if (ctx == NULL) {
    abort();
  }
  auth_config_retain(config);
  ctx->config = config;
  return ctx;
}

option_server_credentials
TLS13_OpenSSL_server_credentials_new(
    uint8_t *certificate_chain,
    size_t certificate_chain_len,
    uint8_t *private_key,
    size_t private_key_len) {
  option_server_credentials result = {
      .tag = CUSTARD_NONE,
      .val.Some = NULL,
  };
  tls13_server_credentials *raw =
      tls13_openssl_server_credentials_new(
          certificate_chain,
          certificate_chain_len,
          private_key,
          private_key_len);
  if (raw == NULL) {
    return result;
  }

  TLS13_OpenSSL_server_credentials creds = calloc(1, sizeof *creds);
  if (creds == NULL) {
    tls13_openssl_server_credentials_free(raw);
    return result;
  }
  atomic_init(&creds->references, (size_t)1u);
  creds->raw = raw;
  result.tag = CUSTARD_SOME;
  result.val.Some = creds;
  return result;
}

TLS13_OpenSSL_server_credentials
TLS13_OpenSSL_server_credentials_clone(
    TLS13_OpenSSL_server_credentials creds) {
  if (creds == NULL) {
    abort();
  }
  (void)atomic_fetch_add_explicit(
      &creds->references, (size_t)1u, memory_order_relaxed);
  return creds;
}

option_size
TLS13_OpenSSL_sign_certificate_verify(
    TLS13_OpenSSL_server_credentials creds,
    uint8_t *input,
    size_t input_len,
    uint8_t *signature,
    size_t signature_capacity) {
  option_size result = {
      .tag = CUSTARD_NONE,
      .val.Some = 0,
  };
  size_t signature_len = 0;
  if (creds != NULL &&
      tls13_openssl_server_sign_rsa_pss_sha256(
          creds->raw,
          input,
          input_len,
          signature,
          signature_capacity,
          &signature_len)) {
    result.tag = CUSTARD_SOME;
    result.val.Some = signature_len;
  }
  return result;
}

/* Parity gap G5: expose the credential's signature scheme so the verified
   server can negotiate the scheme its own key supports. */
uint16_t
TLS13_OpenSSL_server_credential_signature_scheme(
    TLS13_OpenSSL_server_credentials creds) {
  if (creds == NULL) {
    abort();
  }
  return tls13_openssl_server_credential_signature_scheme(creds->raw);
}

option_size
TLS13_OpenSSL_copy_server_certificate_chain(
    TLS13_OpenSSL_server_credentials creds,
    uint8_t *out,
    size_t out_capacity) {
  option_size result = {
      .tag = CUSTARD_NONE,
      .val.Some = 0,
  };
  size_t out_len = 0;
  if (creds != NULL &&
      tls13_openssl_server_copy_certificate_chain(
          creds->raw,
          out,
          out_capacity,
          &out_len)) {
    result.tag = CUSTARD_SOME;
    result.val.Some = out_len;
  }
  return result;
}

void TLS13_OpenSSL_auth_config_free(TLS13_OpenSSL_auth_config config) {
  if (config == NULL) {
    return;
  }
  if (atomic_fetch_sub_explicit(
          &config->references, (size_t)1u, memory_order_acq_rel) !=
      (size_t)1u) {
    return;
  }
  free(config);
}

void TLS13_OpenSSL_auth_context_free(TLS13_OpenSSL_auth_context ctx) {
  if (ctx == NULL) {
    return;
  }
  TLS13_OpenSSL_auth_config_free(ctx->config);
  free(ctx);
}

void TLS13_OpenSSL_server_credentials_free(TLS13_OpenSSL_server_credentials creds) {
  if (creds == NULL) {
    return;
  }
  if (atomic_fetch_sub_explicit(
          &creds->references, (size_t)1u, memory_order_acq_rel) !=
      (size_t)1u) {
    return;
  }
  tls13_openssl_server_credentials_free(creds->raw);
  free(creds);
}
