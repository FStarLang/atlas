module TLS13.Crypto.Hybrid

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

friend TLS13.Crypto.Hybrid.Spec

module A = Pulse.Lib.Array
module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module H = TLS13.Crypto.Hybrid.Spec
module CS = TLS13.Crypto.Secret
module Crypto = TLS13.Crypto
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module S8 = Hacl.Secret.UInt8
module Copy = Hacl.Impl.Copy
module Sub = Hacl.Impl.Sub
module Mem = Hacl.Mem
module M = Spec.MLKEM
module P = Spec.MLKEM.Params
module K = Hacl.MLKEM768

(** {2 Pure bridges from hacl-pulse's [Spec.MLKEM] to [H]} *)

let lemma_keygen (sk: B.bytes { B.length sk == 96 })
  : Lemma
      (H.mlkem768_lens ();
       H.mlkem768_keygen_ek (H.client_d sk) (H.client_z sk) ==
         CS.declassify_seq (fst (M.keygen P.mlkem768
                                  (CS.classify_seq (Seq.slice sk 0 32))
                                  (CS.classify_seq (Seq.slice sk 32 64)))) /\
       H.mlkem768_keygen_dk (H.client_d sk) (H.client_z sk) ==
         CS.declassify_seq (snd (M.keygen P.mlkem768
                                  (CS.classify_seq (Seq.slice sk 0 32))
                                  (CS.classify_seq (Seq.slice sk 32 64)))))
  = H.mlkem768_lens ()

let lemma_encaps (ek: B.bytes { B.length ek == 1184 }) (m: B.bytes { B.length m == 32 })
  : Lemma
      (H.mlkem768_lens ();
       H.mlkem768_encaps_ss ek m ==
         CS.declassify_seq (fst (M.encaps P.mlkem768 (CS.classify_seq ek) (CS.classify_seq m))) /\
       H.mlkem768_encaps_ct ek m ==
         CS.declassify_seq (snd (M.encaps P.mlkem768 (CS.classify_seq ek) (CS.classify_seq m))))
  = H.mlkem768_lens ()

let lemma_decaps (dk: B.bytes { B.length dk == 2400 }) (ct: B.bytes { B.length ct == 1088 })
  : Lemma
      (H.mlkem768_lens ();
       H.mlkem768_decaps dk ct ==
         CS.declassify_seq (M.decaps P.mlkem768 (CS.classify_seq dk) (CS.classify_seq ct)))
  = H.mlkem768_lens ()

let lemma_ek_valid (ek: B.bytes { B.length ek == 1184 })
  : Lemma
      (H.mlkem768_lens ();
       H.mlkem768_ek_valid ek <==> M.ek_valid P.mlkem768 (CS.classify_seq ek))
  = H.mlkem768_lens ()

(** {2 Window plumbing} *)

let lemma_window (#t: Type) (w v v': Seq.seq t) (i j: nat)
  : Lemma
      (requires i <= j /\ j <= Seq.length v /\
                Seq.length w == Seq.length v /\ Seq.length v' == j - i /\
                (forall (k: nat). k < Seq.length w ==>
                   Seq.index w k == (if i <= k && k < j
                                     then Seq.index v' (k - i)
                                     else Seq.index v k)))
      (ensures Seq.slice w i j == v' /\
               Seq.slice w 0 i == Seq.slice v 0 i /\
               Seq.slice w j (Seq.length w) == Seq.slice v j (Seq.length v))
  = Seq.lemma_eq_intro (Seq.slice w i j) v';
    Seq.lemma_eq_intro (Seq.slice w 0 i) (Seq.slice v 0 i);
    Seq.lemma_eq_intro (Seq.slice w j (Seq.length w)) (Seq.slice v j (Seq.length v))

(** [Sub.unsub], stated with slices instead of pointwise, so that the
    quantifier stays inside this function. *)
ghost
fn unsub_s (#t: Type0) (a: A.array t)
  (i: nat) (j: nat { i <= j /\ j <= A.length a })
  (b: A.array t { b == A.gsub a i j })
  (#v: erased (Seq.seq t)) (#v': erased (Seq.seq t))
  requires Sub.rest a 1.0R i j v ** A.pts_to b v' **
           pure (Seq.length v == A.length a /\ Seq.length v' == j - i)
  ensures exists* (w: Seq.seq t).
    A.pts_to a w **
    pure (Seq.length w == A.length a /\ Seq.length w == Seq.length v /\
          Seq.slice w i j == Ghost.reveal v' /\
          Seq.slice w 0 i == Seq.slice v 0 i /\
          Seq.slice w j (Seq.length w) == Seq.slice v j (Seq.length v))
{
  Sub.unsub a i j b;
  with w. assert (A.pts_to a w);
  lemma_window #t w v v' i j;
  assert pure (Seq.slice w i j == Ghost.reveal v');
}

let lemma_join (w a b: B.bytes)
  : Lemma
      (requires B.length w == B.length a + B.length b /\
                Seq.slice w 0 (B.length a) == a /\
                Seq.slice w (B.length a) (B.length w) == b)
      (ensures w == Seq.append a b)
  = Seq.lemma_split w (B.length a)

(** Copy the 32 bytes at [off] in [sk] into the secret seed buffer [dst]. *)
fn load_seed (sk: array U8.t) (off: SZ.t) (dst: A.array S8.t)
  requires pts_to sk 'sk_bytes ** A.pts_to dst 'vd **
           pure (Seq.length 'vd == 32 /\ SZ.v off + 32 <= B.length 'sk_bytes)
  ensures exists* vd.
    pts_to sk 'sk_bytes ** A.pts_to dst vd **
    pure (SZ.v off + 32 <= B.length 'sk_bytes /\
          vd == CS.classify_seq (Seq.slice 'sk_bytes (SZ.v off) (SZ.v off + 32)))
{
  A.pts_to_len sk;
  A.pts_to_len dst;
  CS.to_secret sk;
  A.pts_to_len (CS.secret sk);
  Copy.copy_range dst 0sz (CS.secret sk) off 32sz;
  with vd. assert (A.pts_to dst vd);
  Seq.lemma_eq_intro vd (Seq.slice (CS.classify_seq 'sk_bytes) (SZ.v off) (SZ.v off + 32));
  CS.classify_slice 'sk_bytes (SZ.v off) (SZ.v off + 32);
  CS.of_secret sk;
  rewrite pts_to sk (CS.declassify_seq (CS.classify_seq 'sk_bytes)) as pts_to sk 'sk_bytes;
}

(** {2 X25519 at an offset} *)

fn x25519_public_at (sk: array U8.t) (sk_off: SZ.t) (out: array U8.t) (out_off: SZ.t)
  requires pts_to sk 'sk_bytes ** pts_to out 'old **
           pure (SZ.v sk_off + 32 <= B.length 'sk_bytes /\
                 SZ.v out_off + 32 <= B.length 'old)
  ensures exists* w.
    pts_to sk 'sk_bytes ** pts_to out w **
    pure (SZ.v sk_off + 32 <= B.length 'sk_bytes /\
          SZ.v out_off + 32 <= B.length 'old /\
          B.length w == B.length 'old /\
          Seq.slice w (SZ.v out_off) (SZ.v out_off + 32) ==
            C.x25519_public_from_private
              (Seq.slice 'sk_bytes (SZ.v sk_off) (SZ.v sk_off + 32)) /\
          Seq.slice w 0 (SZ.v out_off) == Seq.slice 'old 0 (SZ.v out_off) /\
          Seq.slice w (SZ.v out_off + 32) (B.length w) ==
            Seq.slice 'old (SZ.v out_off + 32) (B.length 'old))
{
  A.pts_to_len sk;
  A.pts_to_len out;
  let sk_end = SZ.add sk_off 32sz;
  let out_end = SZ.add out_off 32sz;
  let xs = Sub.sub sk sk_off sk_end;
  let xo = Sub.sub out out_off out_end;
  Crypto.x25519_public_from_private xs xo;
  Sub.unsub_id sk (SZ.v sk_off) (SZ.v sk_end) xs;
  unsub_s out (SZ.v out_off) (SZ.v out_end) xo;
}

fn x25519_shared_at
  (sk: array U8.t) (sk_off: SZ.t)
  (pk: array U8.t) (pk_off: SZ.t)
  (out: array U8.t) (out_off: SZ.t)
  requires pts_to sk 'sk_bytes ** pts_to pk 'pk_bytes ** pts_to out 'old **
           pure (SZ.v sk_off + 32 <= B.length 'sk_bytes /\
                 SZ.v pk_off + 32 <= B.length 'pk_bytes /\
                 SZ.v out_off + 32 <= B.length 'old)
  returns ok: bool
  ensures exists* w.
    pts_to sk 'sk_bytes ** pts_to pk 'pk_bytes ** pts_to out w **
    pure (SZ.v sk_off + 32 <= B.length 'sk_bytes /\
          SZ.v pk_off + 32 <= B.length 'pk_bytes /\
          SZ.v out_off + 32 <= B.length 'old /\
          B.length w == B.length 'old /\
          (let r = C.x25519_shared (Seq.slice 'sk_bytes (SZ.v sk_off) (SZ.v sk_off + 32))
                                   (Seq.slice 'pk_bytes (SZ.v pk_off) (SZ.v pk_off + 32)) in
           (ok <==> Some? r) /\
           (ok ==> Seq.slice w (SZ.v out_off) (SZ.v out_off + 32) == Some?.v r)) /\
          Seq.slice w 0 (SZ.v out_off) == Seq.slice 'old 0 (SZ.v out_off) /\
          Seq.slice w (SZ.v out_off + 32) (B.length w) ==
            Seq.slice 'old (SZ.v out_off + 32) (B.length 'old))
{
  A.pts_to_len sk;
  A.pts_to_len pk;
  A.pts_to_len out;
  let sk_end = SZ.add sk_off 32sz;
  let pk_end = SZ.add pk_off 32sz;
  let out_end = SZ.add out_off 32sz;
  let xs = Sub.sub sk sk_off sk_end;
  let xp = Sub.sub pk pk_off pk_end;
  let xo = Sub.sub out out_off out_end;
  let ok = Crypto.x25519_shared xs xp xo;
  Sub.unsub_id sk (SZ.v sk_off) (SZ.v sk_end) xs;
  Sub.unsub_id pk (SZ.v pk_off) (SZ.v pk_end) xp;
  unsub_s out (SZ.v out_off) (SZ.v out_end) xo;
  ok
}

(** {2 ML-KEM-768 into windows} *)

(** The client's encapsulation key, regenerated from the seeds in [sk],
    into [out[0, 1184)]. *)
fn mlkem_ek_into (sk: array U8.t) (out: array U8.t)
  requires pts_to sk 'sk_bytes ** pts_to out 'old **
           pure (B.length 'sk_bytes == 96 /\ B.length 'old == 1216)
  ensures exists* w.
    pts_to sk 'sk_bytes ** pts_to out w **
    pure (B.length 'old == 1216 /\ B.length w == 1216 /\
          Seq.slice w 0 1184 == H.mlkem768_keygen_ek (H.client_d 'sk_bytes) (H.client_z 'sk_bytes) /\
          Seq.slice w 1184 1216 == Seq.slice 'old 1184 1216)
{
  H.mlkem768_lens ();
  A.pts_to_len out;
  let zb : S8.t = S8.classify 0uy;
  let mut d = [| zb; 32sz |];
  let mut z = [| zb; 32sz |];
  let mut dk = [| zb; 2400sz |];
  Mem.track d;
  Mem.track z;
  Mem.track dk;
  load_seed sk 0sz d;
  load_seed sk 32sz z;
  CS.to_secret out;
  A.pts_to_len (CS.secret out);
  let ekw = Sub.sub (CS.secret out) 0sz 1184sz;
  K.keypair ekw dk d z;
  unsub_s (CS.secret out) 0 1184 ekw;
  with w. assert (A.pts_to (CS.secret out) w);
  CS.declassify_slice w 0 1184;
  CS.declassify_slice w 1184 1216;
  CS.classify_slice 'old 1184 1216;
  CS.of_secret out;
  lemma_keygen 'sk_bytes;
  Mem.wipe d 32sz;
  Mem.wipe z 32sz;
  Mem.wipe dk 2400sz;
}

(** Encapsulation to the key in [cs[0, 1184)] with the message in
    [sk[0, 32)]: the ciphertext into [ct_out[0, 1088)], the secret into
    [ss_out[0, 32)].  [false], touching nothing, if the key fails the
    FIPS 203 modulus check. *)
fn mlkem_encaps_into
  (sk: array U8.t) (cs: array U8.t) (ct_out: array U8.t) (ss_out: array U8.t)
  requires pts_to sk 'sk_bytes ** pts_to cs 'cs_bytes **
           pts_to ct_out 'old_ct ** pts_to ss_out 'old_ss **
           pure (B.length 'sk_bytes == 64 /\ B.length 'cs_bytes == 1216 /\
                 B.length 'old_ct == 1120 /\ B.length 'old_ss == 64)
  returns valid: bool
  ensures exists* wct wss.
    pts_to sk 'sk_bytes ** pts_to cs 'cs_bytes **
    pts_to ct_out wct ** pts_to ss_out wss **
    pure (B.length 'old_ct == 1120 /\ B.length 'old_ss == 64 /\
          B.length wct == 1120 /\ B.length wss == 64 /\
          (valid <==> H.x25519mlkem768_client_share_ok 'cs_bytes) /\
          Seq.slice wct 1088 1120 == Seq.slice 'old_ct 1088 1120 /\
          Seq.slice wss 32 64 == Seq.slice 'old_ss 32 64 /\
          (valid ==>
            Seq.slice wct 0 1088 ==
              H.mlkem768_encaps_ct (H.share_mlkem 'cs_bytes 1184) (H.server_m 'sk_bytes) /\
            Seq.slice wss 0 32 ==
              H.mlkem768_encaps_ss (H.share_mlkem 'cs_bytes 1184) (H.server_m 'sk_bytes)))
{
  H.mlkem768_lens ();
  A.pts_to_len cs;
  A.pts_to_len ct_out;
  A.pts_to_len ss_out;
  lemma_ek_valid (Seq.slice 'cs_bytes 0 1184);
  lemma_encaps (Seq.slice 'cs_bytes 0 1184) (Seq.slice 'sk_bytes 0 32);
  CS.classify_slice 'cs_bytes 0 1184;
  let zb : S8.t = S8.classify 0uy;
  let mut m = [| zb; 32sz |];
  Mem.track m;
  load_seed sk 0sz m;
  CS.to_secret cs;
  A.pts_to_len (CS.secret cs);
  let ekw = Sub.sub (CS.secret cs) 0sz 1184sz;
  let valid = K.ek_valid ekw;
  if valid {
    CS.to_secret ct_out;
    A.pts_to_len (CS.secret ct_out);
    let ctw = Sub.sub (CS.secret ct_out) 0sz 1088sz;
    CS.to_secret ss_out;
    A.pts_to_len (CS.secret ss_out);
    let ssw = Sub.sub (CS.secret ss_out) 0sz 32sz;
    K.enc ctw ssw ekw m;
    unsub_s (CS.secret ct_out) 0 1088 ctw;
    with wc. assert (A.pts_to (CS.secret ct_out) wc);
    unsub_s (CS.secret ss_out) 0 32 ssw;
    with ws. assert (A.pts_to (CS.secret ss_out) ws);
    CS.declassify_slice wc 0 1088;
    CS.declassify_slice wc 1088 1120;
    CS.declassify_slice ws 0 32;
    CS.declassify_slice ws 32 64;
    CS.classify_slice 'old_ct 1088 1120;
    CS.classify_slice 'old_ss 32 64;
    CS.of_secret ct_out;
    CS.of_secret ss_out;
    Sub.unsub_id (CS.secret cs) 0 1184 ekw;
    CS.of_secret cs;
    rewrite pts_to cs (CS.declassify_seq (CS.classify_seq 'cs_bytes)) as pts_to cs 'cs_bytes;
    Mem.wipe m 32sz;
    true
  } else {
    Sub.unsub_id (CS.secret cs) 0 1184 ekw;
    CS.of_secret cs;
    rewrite pts_to cs (CS.declassify_seq (CS.classify_seq 'cs_bytes)) as pts_to cs 'cs_bytes;
    Mem.wipe m 32sz;
    false
  }
}

(** Decapsulation of [server_share[0, 1088)] with the key regenerated from
    the seeds in [sk], into [ss_out[0, 32)]. *)
fn mlkem_decaps_into (sk: array U8.t) (server_share: array U8.t) (ss_out: array U8.t)
  requires pts_to sk 'sk_bytes ** pts_to server_share 'sv_bytes ** pts_to ss_out 'old **
           pure (B.length 'sk_bytes == 96 /\ B.length 'sv_bytes == 1120 /\ B.length 'old == 64)
  ensures exists* w.
    pts_to sk 'sk_bytes ** pts_to server_share 'sv_bytes ** pts_to ss_out w **
    pure (B.length 'old == 64 /\ B.length w == 64 /\
          Seq.slice w 0 32 ==
            H.mlkem768_decaps (H.mlkem768_keygen_dk (H.client_d 'sk_bytes) (H.client_z 'sk_bytes))
                              (H.share_mlkem 'sv_bytes 1088) /\
          Seq.slice w 32 64 == Seq.slice 'old 32 64)
{
  H.mlkem768_lens ();
  A.pts_to_len ss_out;
  lemma_keygen 'sk_bytes;
  lemma_decaps (H.mlkem768_keygen_dk (H.client_d 'sk_bytes) (H.client_z 'sk_bytes))
               (Seq.slice 'sv_bytes 0 1088);
  CS.classify_slice 'sv_bytes 0 1088;
  let zb : S8.t = S8.classify 0uy;
  let mut d = [| zb; 32sz |];
  let mut z = [| zb; 32sz |];
  let mut ek = [| zb; 1184sz |];
  let mut dk = [| zb; 2400sz |];
  Mem.track d;
  Mem.track z;
  Mem.track dk;
  load_seed sk 0sz d;
  load_seed sk 32sz z;
  K.keypair ek dk d z;
  CS.to_secret server_share;
  A.pts_to_len (CS.secret server_share);
  let ctw = Sub.sub (CS.secret server_share) 0sz 1088sz;
  CS.to_secret ss_out;
  A.pts_to_len (CS.secret ss_out);
  let ssw = Sub.sub (CS.secret ss_out) 0sz 32sz;
  K.dec ssw ctw dk;
  unsub_s (CS.secret ss_out) 0 32 ssw;
  with w. assert (A.pts_to (CS.secret ss_out) w);
  CS.declassify_slice w 0 32;
  CS.declassify_slice w 32 64;
  CS.classify_slice 'old 32 64;
  CS.of_secret ss_out;
  Sub.unsub_id (CS.secret server_share) 0 1088 ctw;
  CS.of_secret server_share;
  rewrite pts_to server_share (CS.declassify_seq (CS.classify_seq 'sv_bytes))
       as pts_to server_share 'sv_bytes;
  Mem.wipe d 32sz;
  Mem.wipe z 32sz;
  Mem.wipe dk 2400sz;
}

(** {2 The hybrid} *)

fn x25519mlkem768_client_public (sk: array U8.t) (out: array U8.t)
  requires pts_to sk 'sk_bytes **
           pts_to out 'old **
           pure (B.length 'sk_bytes == 96 /\ B.length 'old == 1216)
  ensures pts_to sk 'sk_bytes **
          pts_to out (H.x25519mlkem768_client_public 'sk_bytes)
{
  mlkem_ek_into sk out;
  with w1. assert (pts_to out w1);
  x25519_public_at sk 64sz out 1184sz;
  with w2. assert (pts_to out w2);
  lemma_join w2
    (H.mlkem768_keygen_ek (H.client_d 'sk_bytes) (H.client_z 'sk_bytes))
    (C.x25519_public_from_private (H.client_x 'sk_bytes));
  rewrite pts_to out w2 as pts_to out (H.x25519mlkem768_client_public 'sk_bytes);
}

fn x25519mlkem768_server_encaps
  (sk: array U8.t)
  (client_share: array U8.t)
  (share_out: array U8.t)
  (ss_out: array U8.t)
  requires pts_to sk 'sk_bytes **
           pts_to client_share 'cs_bytes **
           pts_to share_out 'old_share **
           pts_to ss_out 'old_ss **
           pure (B.length 'sk_bytes == 64 /\
                 B.length 'cs_bytes == 1216 /\
                 B.length 'old_share == 1120 /\
                 B.length 'old_ss == 64)
  returns ok: bool
  ensures exists* share ss.
          pts_to sk 'sk_bytes **
          pts_to client_share 'cs_bytes **
          pts_to share_out share **
          pts_to ss_out ss **
          pure (B.length share == 1120 /\
                B.length ss == 64 /\
                (ok <==> Some? (H.x25519mlkem768_server_shared 'sk_bytes 'cs_bytes)) /\
                (ok ==>
                  Some? (H.x25519mlkem768_server_share 'sk_bytes 'cs_bytes) /\
                  share == Some?.v (H.x25519mlkem768_server_share 'sk_bytes 'cs_bytes) /\
                  ss == Some?.v (H.x25519mlkem768_server_shared 'sk_bytes 'cs_bytes)))
{
  let valid = mlkem_encaps_into sk client_share share_out ss_out;
  if valid {
    with wc1. assert (pts_to share_out wc1);
    with ws1. assert (pts_to ss_out ws1);
    x25519_public_at sk 32sz share_out 1088sz;
    with wc2. assert (pts_to share_out wc2);
    let ok = x25519_shared_at sk 32sz client_share 1184sz ss_out 32sz;
    with ws2. assert (pts_to ss_out ws2);
    lemma_join wc2
      (H.mlkem768_encaps_ct (H.share_mlkem 'cs_bytes 1184) (H.server_m 'sk_bytes))
      (C.x25519_public_from_private (H.server_x 'sk_bytes));
    if ok {
      lemma_join ws2
        (H.mlkem768_encaps_ss (H.share_mlkem 'cs_bytes 1184) (H.server_m 'sk_bytes))
        (Some?.v (C.x25519_shared (H.server_x 'sk_bytes) (H.share_x25519 'cs_bytes 1184)));
      true
    } else {
      false
    }
  } else {
    false
  }
}

fn x25519mlkem768_client_shared
  (sk: array U8.t)
  (server_share: array U8.t)
  (ss_out: array U8.t)
  requires pts_to sk 'sk_bytes **
           pts_to server_share 'ss_bytes **
           pts_to ss_out 'old **
           pure (B.length 'sk_bytes == 96 /\
                 B.length 'ss_bytes == 1120 /\
                 B.length 'old == 64)
  returns ok: bool
  ensures exists* ss.
          pts_to sk 'sk_bytes **
          pts_to server_share 'ss_bytes **
          pts_to ss_out ss **
          pure (B.length ss == 64 /\
                (ok <==> Some? (H.x25519mlkem768_client_shared 'sk_bytes 'ss_bytes)) /\
                (ok ==> ss == Some?.v (H.x25519mlkem768_client_shared 'sk_bytes 'ss_bytes)))
{
  mlkem_decaps_into sk server_share ss_out;
  let ok = x25519_shared_at sk 64sz server_share 1088sz ss_out 32sz;
  with w2. assert (pts_to ss_out w2);
  if ok {
    lemma_join w2
      (H.mlkem768_decaps (H.mlkem768_keygen_dk (H.client_d 'sk_bytes) (H.client_z 'sk_bytes))
                         (H.share_mlkem 'ss_bytes 1088))
      (Some?.v (C.x25519_shared (H.client_x 'sk_bytes) (H.share_x25519 'ss_bytes 1088)));
    true
  } else {
    false
  }
}
