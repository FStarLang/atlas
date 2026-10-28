#ifndef TLS13_PEM_H
#define TLS13_PEM_H

/*
 * PEM front end.  The verified client sees trust anchors as a concatenation of
 * DER certificates (TLS13.X509.Spec.trust_store); tls13_pem_certificates_to_der
 * decodes every "CERTIFICATE" block of a PEM bundle into that form.  The
 * verified server (TLS13.Impl.ServerCredentials) reads its private key as DER;
 * tls13_pem_private_key_to_der decodes the first PEM private-key block into
 * that form.  The decoding is the verified TLS13.Impl.Pem (specified by
 * TLS13.Pem.Spec); runtime/tls13_pem.c only allocates the result.  It depends
 * on no TLS or crypto library.
 */

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Converts every CERTIFICATE block of a PEM bundle into concatenated DER.  On
   success returns 0 and stores a malloc'd buffer (caller frees) in *out; an
   empty input yields an empty result.  Fails if a non-empty input contains no
   certificate or a malformed block. */
int tls13_pem_certificates_to_der(
    const uint8_t *pem, size_t pem_len, uint8_t **out, size_t *out_len);

/* Converts a private key to DER: DER input (starting with a SEQUENCE tag) is
   copied unchanged; otherwise the first "-----BEGIN ...PRIVATE KEY-----" block
   (PKCS#8 "PRIVATE KEY", PKCS#1 "RSA PRIVATE KEY" or SEC1 "EC PRIVATE KEY") is
   decoded, skipping other blocks such as "EC PARAMETERS".  On success returns
   0 and stores a malloc'd buffer in *out, which the caller must wipe
   (tls13_pem_wipe) and free. */
int tls13_pem_private_key_to_der(
    const uint8_t *key, size_t key_len, uint8_t **out, size_t *out_len);

/* Overwrites a secret buffer in a way the compiler may not elide. */
void tls13_pem_wipe(uint8_t *p, size_t n);

#ifdef __cplusplus
}
#endif

#endif
