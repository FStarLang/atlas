module TLS13.Crypto.Hybrid.Spec

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CS = TLS13.Crypto.Secret
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module M = Spec.MLKEM
module MC = Spec.MLKEM.Correctness
module P = Spec.MLKEM.Params

noextract
let c (s: B.bytes) : GTot (r: Seq.seq S8.t { Seq.length r == B.length s }) = CS.classify_seq s

noextract
let d (s: Seq.seq S8.t) : GTot (r: B.bytes { B.length r == Seq.length s }) = CS.declassify_seq s

let mlkem768_lens ()
  : Lemma (P.ek_len P.mlkem768 == 1184 /\
           P.dk_len P.mlkem768 == 2400 /\
           P.ct_len P.mlkem768 == 1088)
  = assert_norm (P.ek_len P.mlkem768 == 1184);
    assert_norm (P.dk_len P.mlkem768 == 2400);
    assert_norm (P.ct_len P.mlkem768 == 1088)

let lens_ok (d0 z0: B.bytes) : bool = B.length d0 = 32 && B.length z0 = 32

(** {2 ML-KEM-768} *)

noextract
let keygen768 (d0 z0: B.bytes { lens_ok d0 z0 })
  : GTot (Seq.lseq S8.t (P.ek_len P.mlkem768) & Seq.lseq S8.t (P.dk_len P.mlkem768))
  = M.keygen P.mlkem768 (c d0) (c z0)

let mlkem768_keygen_ek d0 z0 =
  mlkem768_lens ();
  if lens_ok d0 z0 then d (fst (keygen768 d0 z0)) else B.zeros 1184

let mlkem768_keygen_dk d0 z0 =
  mlkem768_lens ();
  if lens_ok d0 z0 then d (snd (keygen768 d0 z0)) else B.zeros 2400

let mlkem768_encaps_ss ek m =
  mlkem768_lens ();
  if B.length ek = 1184 && B.length m = 32
  then d (fst (M.encaps P.mlkem768 (c ek) (c m)))
  else B.zeros 32

let mlkem768_encaps_ct ek m =
  mlkem768_lens ();
  if B.length ek = 1184 && B.length m = 32
  then d (snd (M.encaps P.mlkem768 (c ek) (c m)))
  else B.zeros 1088

let mlkem768_decaps dk ct =
  mlkem768_lens ();
  if B.length dk = 2400 && B.length ct = 1088
  then d (M.decaps P.mlkem768 (c dk) (c ct))
  else B.zeros 32

let mlkem768_ek_valid ek =
  mlkem768_lens ();
  if B.length ek = 1184
  then FStar.IndefiniteDescription.strong_excluded_middle (M.ek_valid P.mlkem768 (c ek))
  else false

let mlkem768_correct_coins d0 z0 m =
  mlkem768_lens ();
  lens_ok d0 z0 /\ B.length m == 32 /\
  MC.noise_ok
    (MC.kpke_noise P.mlkem768 (c d0) (c m)
       (MC.encaps_coins P.mlkem768 (fst (keygen768 d0 z0)) (c m)))

let lemma_mlkem768_keygen_ek_valid d0 z0 =
  mlkem768_lens ();
  MC.keygen_ek_valid P.mlkem768 (c d0) (c z0)

let lemma_mlkem768_correct d0 z0 m =
  mlkem768_lens ();
  MC.mlkem_correct P.mlkem768 (c d0) (c z0) (c m)

(** {2 X25519MLKEM768} *)

let lemma_split (a b: B.bytes)
  : Lemma (share_mlkem (Seq.append a b) (B.length a) == a /\
           share_x25519 (Seq.append a b) (B.length a) == b)
  = Seq.lemma_eq_intro (Seq.slice (Seq.append a b) 0 (B.length a)) a;
    Seq.lemma_eq_intro (Seq.slice (Seq.append a b) (B.length a) (B.length (Seq.append a b))) b

let lemma_x25519mlkem768_agreement csk ssk =
  let ek = mlkem768_keygen_ek (client_d csk) (client_z csk) in
  let cx = C.x25519_public_from_private (client_x csk) in
  let sx = C.x25519_public_from_private (server_x ssk) in
  let ct = mlkem768_encaps_ct ek (server_m ssk) in
  lemma_split ek cx;
  lemma_mlkem768_keygen_ek_valid (client_d csk) (client_z csk);
  lemma_split ct sx;
  C.lemma_x25519_shared_agreement (client_x csk) (server_x ssk) cx sx;
  lemma_mlkem768_correct (client_d csk) (client_z csk) (server_m ssk)
