#ifndef TLS13_PEM_H
#define TLS13_PEM_H

/*
 * Untrusted PEM front end for trust anchors.  The verified client sees trust
 * anchors as a concatenation of DER certificates (TLS13.X509.Spec.trust_store);
 * this decodes every "CERTIFICATE" block of a PEM bundle into that form.  It
 * depends on no TLS or crypto library.
 */

#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

static inline int tls13_pem_b64_value(uint8_t c) {
  if (c >= 'A' && c <= 'Z') return c - 'A';
  if (c >= 'a' && c <= 'z') return c - 'a' + 26;
  if (c >= '0' && c <= '9') return c - '0' + 52;
  if (c == '+') return 62;
  if (c == '/') return 63;
  return -1;
}

static inline const uint8_t *tls13_pem_find(
    const uint8_t *hay, size_t hay_len, const char *needle) {
  size_t n = strlen(needle);
  if (n == 0u || hay_len < n) {
    return NULL;
  }
  for (size_t i = 0u; i + n <= hay_len; i++) {
    if (memcmp(hay + i, needle, n) == 0) {
      return hay + i;
    }
  }
  return NULL;
}

/* Decodes the base64 body [body, body + body_len) into out (capacity at least
   body_len * 3 / 4).  Whitespace is skipped; anything else malformed fails.
   Returns the decoded length, or (size_t)-1 on error. */
static inline size_t tls13_pem_b64_decode(
    const uint8_t *body, size_t body_len, uint8_t *out) {
  uint32_t acc = 0u;
  size_t bits = 0u, len = 0u, pad = 0u;
  for (size_t i = 0u; i < body_len; i++) {
    uint8_t c = body[i];
    if (c == ' ' || c == '\t' || c == '\r' || c == '\n') {
      continue;
    }
    if (c == '=') {
      pad++;
      continue;
    }
    int v = tls13_pem_b64_value(c);
    if (v < 0 || pad != 0u) {
      return (size_t)-1;
    }
    acc = (acc << 6) | (uint32_t)v;
    bits += 6u;
    if (bits >= 8u) {
      bits -= 8u;
      out[len++] = (uint8_t)(acc >> bits);
    }
  }
  if (pad > 2u || bits >= 6u) {
    return (size_t)-1;
  }
  return len;
}

/* Converts every CERTIFICATE block of a PEM bundle into concatenated DER.  On
   success returns 0 and stores a malloc'd buffer (caller frees) in *out; an
   empty input yields an empty result.  Fails if a non-empty input contains no
   certificate or a malformed block. */
static inline int tls13_pem_certificates_to_der(
    const uint8_t *pem, size_t pem_len, uint8_t **out, size_t *out_len) {
  static const char begin[] = "-----BEGIN CERTIFICATE-----";
  static const char end[] = "-----END CERTIFICATE-----";
  if (out == NULL || out_len == NULL || (pem == NULL && pem_len != 0u)) {
    return 1;
  }
  *out = NULL;
  *out_len = 0u;
  uint8_t *der = (uint8_t *)malloc(pem_len == 0u ? 1u : pem_len);
  if (der == NULL) {
    return 1;
  }
  size_t der_len = 0u, count = 0u;
  const uint8_t *cursor = pem;
  size_t remaining = pem_len;
  for (;;) {
    const uint8_t *b = tls13_pem_find(cursor, remaining, begin);
    if (b == NULL) {
      break;
    }
    const uint8_t *body = b + sizeof begin - 1u;
    size_t after = remaining - (size_t)(body - cursor);
    const uint8_t *e = tls13_pem_find(body, after, end);
    if (e == NULL) {
      free(der);
      return 1;
    }
    size_t n = tls13_pem_b64_decode(body, (size_t)(e - body), der + der_len);
    if (n == (size_t)-1 || n == 0u) {
      free(der);
      return 1;
    }
    der_len += n;
    count++;
    const uint8_t *next = e + sizeof end - 1u;
    remaining -= (size_t)(next - cursor);
    cursor = next;
  }
  if (pem_len != 0u && count == 0u) {
    free(der);
    return 1;
  }
  *out = der;
  *out_len = der_len;
  return 0;
}

#endif
