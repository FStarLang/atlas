#include "tls13_pem.h"

#include "TLS13.h"

#include <stdlib.h>

/* Custard names option specializations after their payload type; alias the
   generated names here so the rest of this file does not depend on them. */
typedef FStar_Pervasives_Native_option__uintsize option_size;
#define SOME_SIZE FSTAR_PERVASIVES_NATIVE_SOME__UINTSIZE

/* The verified decoders write into a caller-supplied buffer as long as their
   input (the output never exceeds it) and do not modify the input, which their
   signatures do not mark const. */

int tls13_pem_certificates_to_der(
    const uint8_t *pem, size_t pem_len, uint8_t **out, size_t *out_len) {
  if (out == NULL || out_len == NULL || (pem == NULL && pem_len != 0u)) {
    return 1;
  }
  *out = NULL;
  *out_len = 0u;
  uint8_t *der = (uint8_t *)malloc(pem_len == 0u ? 1u : pem_len);
  if (der == NULL) {
    return 1;
  }
  if (pem_len == 0u) {
    /* TLS13.Pem.Spec.certificates_to_der: an empty bundle is empty DER. */
    *out = der;
    return 0;
  }
  option_size r =
      TLS13_Impl_Pem_certificates_to_der((uint8_t *)pem, pem_len, der);
  if (r.tag != SOME_SIZE) {
    free(der);
    return 1;
  }
  *out = der;
  *out_len = r.val.Some;
  return 0;
}

void tls13_pem_wipe(uint8_t *p, size_t n) {
  volatile uint8_t *v = p;
  for (size_t i = 0u; i < n; i++) {
    v[i] = 0u;
  }
}

int tls13_pem_private_key_to_der(
    const uint8_t *key, size_t key_len, uint8_t **out, size_t *out_len) {
  if (out == NULL || out_len == NULL || key == NULL || key_len == 0u) {
    return 1;
  }
  *out = NULL;
  *out_len = 0u;
  uint8_t *der = (uint8_t *)malloc(key_len);
  if (der == NULL) {
    return 1;
  }
  option_size r =
      TLS13_Impl_Pem_private_key_to_der((uint8_t *)key, key_len, der);
  if (r.tag != SOME_SIZE) {
    /* A rejected input may have left partially decoded key material. */
    tls13_pem_wipe(der, key_len);
    free(der);
    return 1;
  }
  *out = der;
  *out_len = r.val.Some;
  return 0;
}
