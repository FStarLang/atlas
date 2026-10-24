/* Verified-server half of the X25519MLKEM768 (RFC 10024) interop test.
 *
 * Accepts one connection on 127.0.0.1:PORT with the extracted server driver,
 * echoes one application record back and closes.  The peer is an OpenSSL 3.5
 * `s_client -groups X25519MLKEM768`, driven by test/interop/hybrid.sh: with
 * the hybrid as the client's only group, the handshake can only complete if
 * the verified server selected it (the server sends no HelloRetryRequest).
 */

#include "tls13_server_driver.h"

#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

static int read_file(const char *path, uint8_t **out, size_t *out_len) {
  FILE *f = fopen(path, "rb");
  if (f == NULL) {
    perror(path);
    return 1;
  }
  if (fseek(f, 0, SEEK_END) != 0) {
    fclose(f);
    return 1;
  }
  long len = ftell(f);
  if (len <= 0) {
    fclose(f);
    return 1;
  }
  rewind(f);
  uint8_t *buf = malloc((size_t)len);
  if (buf == NULL || fread(buf, 1u, (size_t)len, f) != (size_t)len) {
    free(buf);
    fclose(f);
    return 1;
  }
  fclose(f);
  *out = buf;
  *out_len = (size_t)len;
  return 0;
}

int main(int argc, char **argv) {
  if (argc != 4) {
    fprintf(stderr, "usage: %s PORT LEAF_DER LEAF_KEY_PEM\n", argv[0]);
    return 2;
  }
  alarm(30);
  uint16_t port = (uint16_t)strtoul(argv[1], NULL, 10);
  uint8_t *chain = NULL, *key = NULL;
  size_t chain_len = 0, key_len = 0;
  if (read_file(argv[2], &chain, &chain_len) != 0 ||
      read_file(argv[3], &key, &key_len) != 0) {
    return 1;
  }

  tls13_server_driver *server = NULL;
  uint8_t received[TLS13_SERVER_DRIVER_RECEIVE_BUFFER_SIZE];
  size_t received_len = 0;
  int rc = 1;
  if (tls13_server_driver_accept(
          &server, "127.0.0.1", port, chain, chain_len, key, key_len) != 0) {
    fprintf(stderr, "hybrid server peer: accept failed\n");
  } else if (tls13_server_driver_receive_application_data(
                 server, received, sizeof received, &received_len) != 0 ||
             tls13_server_driver_send_application_data(
                 server, received, received_len) != 0 ||
             tls13_server_driver_close(server, false) != 0) {
    fprintf(stderr, "hybrid server peer: %s\n",
            tls13_server_driver_last_error(server));
  } else {
    rc = 0;
  }
  tls13_server_driver_free(server);
  free(chain);
  free(key);
  return rc;
}
