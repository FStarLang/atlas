/*
 * vloop_test.c — end-to-end test of the *verified* YMODEM runners.
 *
 * This exercises the extracted, verified F-star/Pulse runners
 * `ymodem_server_send` (sender) and `ymodem_client_receive` (receiver), both of
 * which run the shared verified loop Common.ProtocolDriver.drive_steps — NOT the
 * unverified rb/sb wrapper loops.  It connects the verified sender to the
 * verified receiver over a socketpair (a bidirectional fd, so the single-fd
 * Common.TCP channel bridges both directions), transfers a file through the
 * verified stop-and-wait ARQ (data blocks + per-block ACKs + EOT), and checks
 * that the receiver reconstructed the original bytes.
 *
 * The data-block core (framing, the recv/emit codecs, the ACK handshake, the
 * state-machine transitions) is the verified, extracted code in
 * YModem_Verified.c.  The YMODEM header block 0 (file name / length) and the
 * initial 'C' solicitation are impl glue that live *outside* the modeled state
 * machine, so this our-sender <-> our-receiver test skips them: the receiver's
 * declared length is passed to the harness, and only the 128-byte data blocks
 * (blocks 1..N) flow through the verified loops.
 */

#include "YModem_Verified.h"
#include "common_tcp_custard.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/wait.h>
#include <signal.h>
#include <unistd.h>

#define YM_BLOCK 128
#define YM_PKT   133
#define YM_PAD   0x1Au /* CTRL-Z */
#define FUEL     100000

int main(int argc, char **argv) {
  if (argc != 2) {
    fprintf(stderr, "usage: vloop_test <file>\n");
    return 2;
  }

  /* Read the whole input file. */
  FILE *in = fopen(argv[1], "rb");
  if (!in) { perror("fopen"); return 1; }
  fseek(in, 0, SEEK_END);
  long flen = ftell(in);
  rewind(in);
  if (flen < 0) { fclose(in); return 1; }
  size_t nblocks = (flen == 0) ? 0 : (size_t)((flen + YM_BLOCK - 1) / YM_BLOCK);
  size_t padded = nblocks * YM_BLOCK;
  uint8_t *infile = calloc(padded ? padded : 1, 1);
  if (!infile) { fclose(in); return 1; }
  if (flen > 0 && fread(infile, 1, (size_t)flen, in) != (size_t)flen) { fclose(in); return 1; }
  fclose(in);
  memset(infile + flen, YM_PAD, padded - (size_t)flen); /* pad the tail block */

  /* A harmless late write to an already-closed peer must not raise SIGPIPE. */
  signal(SIGPIPE, SIG_IGN);

  int sv[2];
  if (socketpair(AF_UNIX, SOCK_STREAM, 0, sv) != 0) { perror("socketpair"); return 1; }

  pid_t pid = fork();
  if (pid < 0) { perror("fork"); return 1; }

  if (pid == 0) {
    /* ── child: the VERIFIED sender ─────────────────────────────────────── */
    close(sv[1]);
    Common_TCP_channel ch = Common_TCP_channel_of_fd(sv[0]);
    ymodem_server_send(ch, infile, nblocks, (size_t)FUEL);
    Common_TCP_close(ch);
    free(infile);
    _exit(0);
  }

  /* ── parent: the VERIFIED receiver ────────────────────────────────────── */
  close(sv[0]);
  Common_TCP_channel ch = Common_TCP_channel_of_fd(sv[1]);
  size_t   outcap = padded ? padded : YM_BLOCK;
  uint8_t *outbuf = calloc(outcap, 1);
  size_t nbytes = ymodem_client_receive(ch, outbuf, outcap, (size_t)FUEL);
  Common_TCP_close(ch);

  int status = 0;
  waitpid(pid, &status, 0);

  /* Check: the receiver reconstructed the original file (compare the declared
     length; the padding of the final block is not part of the file). */
  int ok = (nbytes >= (size_t)flen) && (memcmp(outbuf, infile, (size_t)flen) == 0);
  printf("verified-runner transfer: sent %zu block(s), receiver wrote %zu byte(s); content %s\n",
         nblocks, nbytes, ok ? "MATCH" : "DIFFER");

  free(outbuf); free(infile);
  return ok ? 0 : 1;
}
