module TLS13.Impl.X509.Key

(** Verified extraction of the public key from a DER certificate, against
    [TLS13.Crypto.Spec.certificate_raw_public_key]: the certificate is
    validated and parsed by the everparse-asn1 parser generated from
    [src/asn1/X509.asn], and the key read from its SubjectPublicKeyInfo.
    *)

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
open Pulse.Lib.Trade
open ASN1.Base
open ASN1.Pulse.Rel
open TLS13.Wire.Generated.X509.Impl
open TLS13.Impl.X509.ASN1
open TLS13.Impl.X509.PublicKey

module A = Pulse.Lib.Array
module ASN = TLS13.Impl.X509.ASN1
module E = ASN1.Spec.Content.Enc
module I = ASN1.Spec.Interpreter
module I64 = FStar.Int64
module LP = LowParse.Spec.Base
module LPS = LowParse.Pulse.Base
module PP = ASN1.Pulse.Parse
module S = Pulse.Lib.Slice
module VE = ASN1.Spec.Value.Enc
module WL = ASN1.Pulse.WriteLeaf
module X = TLS13.Wire.Generated.X509
module XP = TLS13.X509.Profile
module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module KS = TLS13.X509.KeySpec
module CL = TLS13.ConnectionLog
module Cast = FStar.Int.Cast
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8

inline_for_extraction noextract
let eq_rsa_oid : eq_from_t KS.rsa_encryption_oid =
  norm [delta_only [`%mk_eq; `%KS.rsa_encryption_oid]; zeta; iota; primops] (mk_eq KS.rsa_encryption_oid)
inline_for_extraction noextract
let eq_der_null : eq_from_t KS.der_null =
  norm [delta_only [`%mk_eq; `%KS.der_null]; zeta; iota; primops] (mk_eq KS.der_null)
inline_for_extraction noextract
let eq_ec_oid : eq_from_t KS.ec_public_key_oid =
  norm [delta_only [`%mk_eq; `%KS.ec_public_key_oid]; zeta; iota; primops] (mk_eq KS.ec_public_key_oid)
inline_for_extraction noextract
let eq_p256 : eq_from_t KS.prime256v1_param =
  norm [delta_only [`%mk_eq; `%KS.prime256v1_param]; zeta; iota; primops] (mk_eq KS.prime256v1_param)
inline_for_extraction noextract
let eq_p384 : eq_from_t KS.secp384r1_param =
  norm [delta_only [`%mk_eq; `%KS.secp384r1_param]; zeta; iota; primops] (mk_eq KS.secp384r1_param)


fn lit_rsa_oid (s: S.slice U8.t) (#pm: perm) (#w: Ghost.erased (Seq.seq U8.t))
  requires S.pts_to s #pm w
  returns r: bool
  ensures S.pts_to s #pm w ** pure (r <==> KS.bytes_is w KS.rsa_encryption_oid)
{
  S.pts_to_len s;
  let r = eq_rsa_oid s 0sz #pm #w;
  assert (pure (Seq.slice w 0 (Seq.length w) `Seq.equal` w));
  r
}

fn lit_der_null (s: S.slice U8.t) (#pm: perm) (#w: Ghost.erased (Seq.seq U8.t))
  requires S.pts_to s #pm w
  returns r: bool
  ensures S.pts_to s #pm w ** pure (r <==> KS.bytes_is w KS.der_null)
{
  S.pts_to_len s;
  let r = eq_der_null s 0sz #pm #w;
  assert (pure (Seq.slice w 0 (Seq.length w) `Seq.equal` w));
  r
}

fn lit_ec_oid (s: S.slice U8.t) (#pm: perm) (#w: Ghost.erased (Seq.seq U8.t))
  requires S.pts_to s #pm w
  returns r: bool
  ensures S.pts_to s #pm w ** pure (r <==> KS.bytes_is w KS.ec_public_key_oid)
{
  S.pts_to_len s;
  let r = eq_ec_oid s 0sz #pm #w;
  assert (pure (Seq.slice w 0 (Seq.length w) `Seq.equal` w));
  r
}

fn lit_p256 (s: S.slice U8.t) (#pm: perm) (#w: Ghost.erased (Seq.seq U8.t))
  requires S.pts_to s #pm w
  returns r: bool
  ensures S.pts_to s #pm w ** pure (r <==> KS.bytes_is w KS.prime256v1_param)
{
  S.pts_to_len s;
  let r = eq_p256 s 0sz #pm #w;
  assert (pure (Seq.slice w 0 (Seq.length w) `Seq.equal` w));
  r
}

fn lit_p384 (s: S.slice U8.t) (#pm: perm) (#w: Ghost.erased (Seq.seq U8.t))
  requires S.pts_to s #pm w
  returns r: bool
  ensures S.pts_to s #pm w ** pure (r <==> KS.bytes_is w KS.secp384r1_param)
{
  S.pts_to_len s;
  let r = eq_p384 s 0sz #pm #w;
  assert (pure (Seq.slice w 0 (Seq.length w) `Seq.equal` w));
  r
}

#push-options "--z3rlimit 40"
fn copy_magnitude (s: S.slice U8.t) (#pm: perm) (#w: Ghost.erased (Seq.seq U8.t))
  (dst: A.array U8.t) (cap: SZ.t) (#d: Ghost.erased (Seq.seq U8.t))
  requires S.pts_to s #pm w ** A.pts_to dst d ** pure (Seq.length d == SZ.v cap)
  returns n: SZ.t
  ensures S.pts_to s #pm w ** (exists* d'. A.pts_to dst d' **
          pure (Seq.length d' == SZ.v cap /\ SZ.v n <= SZ.v cap /\
                (SZ.v n > 0 ==> KS.uint_magnitude w == Some (Seq.slice d' 0 (SZ.v n)))))
{
  S.pts_to_len s;
  let len = S.len s;
  if (len = 0sz) {
    0sz
  } else {
    let b0 = S.(s.(0sz));
    if (U8.gte b0 0x80uy) {
      0sz
    } else {
      let st = (if (b0 = 0uy && SZ.gt len 1sz) then 1sz else 0sz);
      let n = SZ.sub len st;
      if (SZ.gt n cap) {
        0sz
      } else {
        let mut i = 0sz;
        while (let vi = !i; SZ.lt vi n)
        invariant exists* (vi: SZ.t) (d': Seq.seq U8.t).
          pts_to i vi ** A.pts_to dst d' ** S.pts_to s #pm w **
          pure (SZ.v vi <= SZ.v n /\ Seq.length d' == SZ.v cap /\
                (forall (k: nat). k < SZ.v vi ==> Seq.index d' k == Seq.index w (SZ.v st + k)))
        decreases (SZ.v n - SZ.v (!i))
        {
          let vi = !i;
          let x = S.(s.(SZ.add st vi));
          A.(dst.(vi) <- x);
          i := SZ.add vi 1sz;
        };
        with d'. assert (A.pts_to dst d');
        assert (pure (Seq.equal (Seq.slice d' 0 (SZ.v n)) (Seq.slice w (SZ.v st) (Seq.length w))));
        assert (pure (Seq.equal (Seq.slice w 0 (Seq.length w)) w));
        n
      }
    }
  }
}
#pop-options

let ib = asn1_any_integer_bound

#push-options "--z3rlimit 40"
fn int_magnitude (x: asn1_int_impl) (#pm: perm) (#y: Ghost.erased (asn1_integer_t ib))
  (dst: A.array U8.t) (cap: SZ.t) (#d: Ghost.erased (Seq.seq U8.t))
  requires asn1_int_rel ib pm x y ** A.pts_to dst d ** pure (Seq.length d == SZ.v cap)
  returns n: SZ.t
  ensures asn1_int_rel ib pm x y ** (exists* d'. A.pts_to dst d' **
          pure (Seq.length d' == SZ.v cap /\ SZ.v n <= SZ.v cap /\
                (SZ.v n > 0 ==> KS.uint_magnitude (KS.int_bytes y) == Some (Seq.slice d' 0 (SZ.v n)))))
{
  match x {
    Small i -> {
      rewrite (asn1_int_rel ib pm x y) as (pure (I64.v i == reveal y));
      let mut tmp = [| 0uy; 8sz |];
      let ts = S.from_array tmp 8sz;
      let mut pos = 8sz;
      let ok = WL.r2l_write_i64 ib i y ts pos;
      if ok {
        let p = !pos;
        with v'. assert (S.pts_to ts v');
        S.pts_to_len ts;
        let parts = S.split ts p;
        match parts {
          Mktuple2 lo hi -> {
            assert (pure (Seq.equal (Seq.slice v' (SZ.v p) 8) (KS.int_bytes y)));
            let n = copy_magnitude hi dst cap;
            S.join lo hi ts;
            S.to_array ts;
            rewrite (pure (I64.v i == reveal y)) as (asn1_int_rel ib pm x y);
            n
          }
        }
      } else {
        S.to_array ts;
        rewrite (pure (I64.v i == reveal y)) as (asn1_int_rel ib pm x y);
        0sz
      }
    }
    Big sl -> {
      rewrite (asn1_int_rel ib pm x y) as (prel_slice_ser (E.integer_enc ib) pm sl y ** pure (~ (fits_i64 y)));
      unfold (prel_slice_ser (E.integer_enc ib) pm sl y);
      let n = copy_magnitude sl dst cap;
      fold (prel_slice_ser (E.integer_enc ib) pm sl y);
      rewrite (prel_slice_ser (E.integer_enc ib) pm sl y ** pure (~ (fits_i64 y))) as (asn1_int_rel ib pm x y);
      n
    }
  }
}
#pop-options

#push-options "--z3rlimit 60"
(* The modulus and exponent magnitudes of an RSAPublicKey that is all of [s]. *)
fn rsa_key (s: S.slice U8.t) (#pm: perm) (#w: Ghost.erased (Seq.seq U8.t))
  (km: A.array U8.t) (kcap: SZ.t) (#dk: Ghost.erased (Seq.seq U8.t))
  (ke: A.array U8.t) (ecap: SZ.t) (#de: Ghost.erased (Seq.seq U8.t))
  requires S.pts_to s #pm w ** A.pts_to km dk ** A.pts_to ke de **
           pure (Seq.length dk == SZ.v kcap /\ Seq.length de == SZ.v ecap)
  returns r: (SZ.t & SZ.t)
  ensures S.pts_to s #pm w ** (exists* dk' de'. A.pts_to km dk' ** A.pts_to ke de' **
          pure (Seq.length dk' == SZ.v kcap /\ Seq.length de' == SZ.v ecap /\
                SZ.v (fst r) <= SZ.v kcap /\ SZ.v (snd r) <= SZ.v ecap /\
                (SZ.v (fst r) > 0 /\ SZ.v (snd r) > 0 ==>
                  (match XP.parse_full X.k_RSAPublicKey w with
                   | Some k -> KS.rsa_raw k == Some (C.RawRsa (Seq.slice dk' 0 (SZ.v (fst r)))
                                                                 (Seq.slice de' 0 (SZ.v (snd r))))
                   | None -> False))))
{
  S.pts_to_len s;
  let mut off = 0sz;
  let ok = validate_RSAPublicKey s off;
  let o = !off;
  if (ok && o = S.len s) {
    assert (pure (Seq.equal (Seq.slice w 0 (Seq.length w)) w));
    let v : Ghost.erased (ASN1.Base.asn1_t X.k_RSAPublicKey) =
      Ghost.hide (fst (Some?.v (LP.parse (I.asn1_as_parser X.k_RSAPublicKey) w)));
    let x = parse_RSAPublicKey s #pm #w #v;
    rsa_eq pm x v;
    rewrite (arel true d_RSAPublicKey pm x v) as (rsa_rel pm x v);
    unfold rsa_rel;
    let n = int_magnitude x.modulus km kcap;
    let e = int_magnitude x.publicExponent ke ecap;
    fold (rsa_rel pm x v);
    rewrite (rsa_rel pm x v) as (arel true d_RSAPublicKey pm x v);
    elim_trade (arel true d_RSAPublicKey pm x v) (S.pts_to s #pm w);
    (n, e)
  } else {
    (0sz, 0sz)
  }
}
#pop-options

#push-options "--z3rlimit 40"
(* The [n]-byte uncompressed EC point that is all of [s], without its 0x04 prefix. *)
fn ec_key (s: S.slice U8.t) (#pm: perm) (#w: Ghost.erased (Seq.seq U8.t)) (n: SZ.t)
  (dst: A.array U8.t) (cap: SZ.t) (#d: Ghost.erased (Seq.seq U8.t))
  requires S.pts_to s #pm w ** A.pts_to dst d ** pure (Seq.length d == SZ.v cap /\ SZ.v n > 0 /\ SZ.fits (SZ.v n + 1))
  returns r: bool
  ensures S.pts_to s #pm w ** (exists* d'. A.pts_to dst d' **
          pure (Seq.length d' == SZ.v cap /\ (r ==> SZ.v n <= SZ.v cap /\
                KS.ec_point w (SZ.v n) == Some (Seq.slice d' 0 (SZ.v n)))))
{
  S.pts_to_len s;
  let len = S.len s;
  if (len = SZ.add n 1sz && SZ.lte n cap) {
    let b0 = S.(s.(0sz));
    if (b0 = 0x04uy) {
      let mut i = 0sz;
      while (let vi = !i; SZ.lt vi n)
      invariant exists* (vi: SZ.t) (d': Seq.seq U8.t).
        pts_to i vi ** A.pts_to dst d' ** S.pts_to s #pm w **
        pure (SZ.v vi <= SZ.v n /\ Seq.length d' == SZ.v cap /\
              (forall (k: nat). k < SZ.v vi ==> Seq.index d' k == Seq.index w (1 + k)))
      decreases (SZ.v n - SZ.v (!i))
      {
        let vi = !i;
        let x = S.(s.(SZ.add 1sz vi));
        A.(dst.(vi) <- x);
        i := SZ.add vi 1sz;
      };
      with d'. assert (A.pts_to dst d');
      assert (pure (Seq.equal (Seq.slice d' 0 (SZ.v n)) (Seq.slice w 1 (SZ.v n + 1))));
      true
    } else {
      false
    }
  } else {
    false
  }
}
#pop-options

type key_out = { kind: U8.t; n: SZ.t; e: SZ.t }

let no_key : key_out = { kind = 0uy; n = 0sz; e = 0sz }

let out_ok (o: option C.raw_public_key) (r: key_out) (dk de: Seq.seq U8.t) : prop =
  SZ.v r.n <= Seq.length dk /\ SZ.v r.e <= Seq.length de /\
  (U8.v r.kind == 1 ==> o == Some (C.RawRsa (Seq.slice dk 0 (SZ.v r.n)) (Seq.slice de 0 (SZ.v r.e)))) /\
  (U8.v r.kind == 2 ==> o == Some (C.RawP256 (Seq.slice dk 0 (SZ.v r.n)))) /\
  (U8.v r.kind == 3 ==> o == Some (C.RawP384 (Seq.slice dk 0 (SZ.v r.n))))

let no_key_ok (o: option C.raw_public_key) (dk de: Seq.seq U8.t)
: Lemma (out_ok o no_key dk de)
= assert_norm (U8.v no_key.kind == 0)

let bits_raw (rsa p256 p384: bool) (u: U8.t) (b: Seq.seq U8.t) : GTot (option C.raw_public_key) =
  if u <> 0uy then None
  else if rsa then
    (match XP.parse_full X.k_RSAPublicKey b with Some k -> KS.rsa_raw k | None -> None)
  else if p256 then
    (match KS.ec_point b 64 with Some p -> Some (C.RawP256 p) | None -> None)
  else if p384 then
    (match KS.ec_point b 96 with Some p -> Some (C.RawP384 p) | None -> None)
  else None

let rsa_out (p256 p384: bool) (w: Seq.seq U8.t) (n e: SZ.t) (dk de: Seq.seq U8.t)
: Lemma (requires SZ.v n > 0 /\ SZ.v e > 0 /\ SZ.v n <= Seq.length dk /\ SZ.v e <= Seq.length de /\
                  (match XP.parse_full X.k_RSAPublicKey w with
                   | Some k -> KS.rsa_raw k == Some (C.RawRsa (Seq.slice dk 0 (SZ.v n)) (Seq.slice de 0 (SZ.v e)))
                   | None -> False))
        (ensures out_ok (bits_raw true p256 p384 0uy w) (Mkkey_out 1uy n e) dk de)
= assert (bits_raw true p256 p384 0uy w ==
          (match XP.parse_full X.k_RSAPublicKey w with Some k -> KS.rsa_raw k | None -> None))
    by (FStar.Tactics.norm [delta_only [`%bits_raw]; iota; primops]; FStar.Tactics.trefl ());
  let o = bits_raw true p256 p384 0uy w in
  let r = Mkkey_out 1uy n e in
  assert (o == Some (C.RawRsa (Seq.slice dk 0 (SZ.v n)) (Seq.slice de 0 (SZ.v e))));
  assert (U8.v r.kind == 1);
  assert (SZ.v r.n <= Seq.length dk);
  assert (r.n == n /\ r.e == e);
  assert (out_ok o r dk de)

#push-options "--z3rlimit 60"
fn bits_key (rsa p256 p384: bool) (u: U8.t) (s: S.slice U8.t) (#pm: perm) (#w: Ghost.erased (Seq.seq U8.t))
  (key: A.array U8.t) (kcap: SZ.t) (#dk: Ghost.erased (Seq.seq U8.t))
  (exp: A.array U8.t) (ecap: SZ.t) (#de: Ghost.erased (Seq.seq U8.t))
  requires S.pts_to s #pm w ** A.pts_to key dk ** A.pts_to exp de **
           pure (Seq.length dk == SZ.v kcap /\ Seq.length de == SZ.v ecap)
  returns r: key_out
  ensures S.pts_to s #pm w ** (exists* dk' de'. A.pts_to key dk' ** A.pts_to exp de' **
          pure (Seq.length dk' == SZ.v kcap /\ Seq.length de' == SZ.v ecap /\
                out_ok (bits_raw rsa p256 p384 u w) r dk' de'))
{
  if (u <> 0uy) {
    no_key
  } else if rsa {
    let r = rsa_key s key kcap exp ecap;
    if (SZ.gt (fst r) 0sz && SZ.gt (snd r) 0sz) {
      with dk' de'. assert (A.pts_to key dk' ** A.pts_to exp de');
      rsa_out p256 p384 w (fst r) (snd r) dk' de';
      Mkkey_out 1uy (fst r) (snd r)
    } else {
      no_key
    }
  } else if p256 {
    let ok = ec_key s 64sz key kcap;
    if ok { Mkkey_out 2uy 64sz 0sz } else { no_key }
  } else if p384 {
    let ok = ec_key s 96sz key kcap;
    if ok { Mkkey_out 3uy 96sz 0sz } else { no_key }
  } else {
    no_key
  }
}
#pop-options

let spki_bits (y: XP.spki)
: Lemma (KS.spki_raw_public_key y ==
         bits_raw (KS.oid_is (XP.alg_oid (XP.spki_alg y)) KS.rsa_encryption_oid &&
                   KS.params_are (XP.alg_params (XP.spki_alg y)) KS.der_null)
                  (KS.oid_is (XP.alg_oid (XP.spki_alg y)) KS.ec_public_key_oid &&
                   KS.params_are (XP.alg_params (XP.spki_alg y)) KS.prime256v1_param)
                  (KS.oid_is (XP.alg_oid (XP.spki_alg y)) KS.ec_public_key_oid &&
                   KS.params_are (XP.alg_params (XP.spki_alg y)) KS.secp384r1_param)
                  (BYTES_WITH_UNUSEDBITS?.unused (XP.spki_key y))
                  (BYTES_WITH_UNUSEDBITS?.b (XP.spki_key y)))
= ()

#push-options "--z3rlimit 60"
fn spki_key (x: t_SubjectPublicKeyInfo) (#pm: perm) (#y: Ghost.erased XP.spki)
  (key: A.array U8.t) (kcap: SZ.t) (#dk: Ghost.erased (Seq.seq U8.t))
  (exp: A.array U8.t) (ecap: SZ.t) (#de: Ghost.erased (Seq.seq U8.t))
  requires spki_rel pm x y ** A.pts_to key dk ** A.pts_to exp de **
           pure (Seq.length dk == SZ.v kcap /\ Seq.length de == SZ.v ecap)
  returns r: key_out
  ensures spki_rel pm x y ** (exists* dk' de'. A.pts_to key dk' ** A.pts_to exp de' **
          pure (Seq.length dk' == SZ.v kcap /\ Seq.length de' == SZ.v ecap /\
                out_ok (KS.spki_raw_public_key y) r dk' de'))
{
  unfold spki_rel;
  let rsa = alg_is KS.rsa_encryption_oid lit_rsa_oid KS.der_null lit_der_null x.algorithm;
  let p256 = alg_is KS.ec_public_key_oid lit_ec_oid KS.prime256v1_param lit_p256 x.algorithm;
  let p384 = alg_is KS.ec_public_key_oid lit_ec_oid KS.secp384r1_param lit_p384 x.algorithm;
  unfold asn1_bitstring_rel;
  let r = bits_key rsa p256 p384 x.subjectPublicKey.unused x.subjectPublicKey.bytes key kcap exp ecap;
  fold (asn1_bitstring_rel pm x.subjectPublicKey (snd y));
  fold (spki_rel pm x y);
  spki_bits y;
  r
}
#pop-options

let whole_cert (w: Seq.seq U8.t) (o: SZ.t)
: Lemma (requires LPS.validator_success #asn1_strong_parser_kind (I.asn1_as_parser X.k_Certificate) 0sz w o /\
                  SZ.v o == Seq.length w)
        (ensures (let v = fst (Some?.v (LP.parse (I.asn1_as_parser X.k_Certificate) w)) in
                  XP.parse_full X.k_Certificate w == Some v /\
                  PP.parsed #asn1_strong_parser_kind (I.asn1_as_parser X.k_Certificate) w v))
= assert (Seq.equal (Seq.slice w 0 (Seq.length w)) w)

let cert_out (w: Seq.seq U8.t) (v: XP.certificate)
: Lemma (requires XP.parse_full X.k_Certificate w == Some v)
        (ensures KS.certificate_key w == KS.spki_raw_public_key (XP.tbs_spki (XP.cert_tbs v)))
= ()

#push-options "--z3rlimit 80"
fn cert_key (s: S.slice U8.t) (#pm: perm) (#w: Ghost.erased (Seq.seq U8.t))
  (key: A.array U8.t) (kcap: SZ.t) (#dk: Ghost.erased (Seq.seq U8.t))
  (exp: A.array U8.t) (ecap: SZ.t) (#de: Ghost.erased (Seq.seq U8.t))
  requires S.pts_to s #pm w ** A.pts_to key dk ** A.pts_to exp de **
           pure (Seq.length dk == SZ.v kcap /\ Seq.length de == SZ.v ecap)
  returns r: key_out
  ensures S.pts_to s #pm w ** (exists* dk' de'. A.pts_to key dk' ** A.pts_to exp de' **
          pure (Seq.length dk' == SZ.v kcap /\ Seq.length de' == SZ.v ecap /\
                out_ok (KS.certificate_key w) r dk' de'))
{
  S.pts_to_len s;
  let mut off = 0sz;
  let ok = validate_Certificate s off;
  let o = !off;
  if (ok && o = S.len s) {
    whole_cert w o;
    let v : Ghost.erased (ASN1.Base.asn1_t X.k_Certificate) =
      Ghost.hide (fst (Some?.v (LP.parse (I.asn1_as_parser X.k_Certificate) w)));
    let x = parse_Certificate s #pm #w #v;
    cert_unpack ();
    unfold cert_flat;
    unfold tbs_rel;
    let pk = x.tbsCertificate.value.subjectPublicKeyInfo;
    spki_eq (pm /. 2.0R) pk (XP.tbs_spki (XP.cert_tbs v));
    rewrite (arel true d_SubjectPublicKeyInfo (pm /. 2.0R) x.tbsCertificate.value.subjectPublicKeyInfo
               (fst (snd (snd (snd (snd (snd (snd (fst (reveal v))))))))))
         as (spki_rel (pm /. 2.0R) pk (XP.tbs_spki (XP.cert_tbs v)));
    let r = spki_key pk key kcap exp ecap;
    rewrite (spki_rel (pm /. 2.0R) pk (XP.tbs_spki (XP.cert_tbs v)))
         as (arel true d_SubjectPublicKeyInfo (pm /. 2.0R) x.tbsCertificate.value.subjectPublicKeyInfo
               (fst (snd (snd (snd (snd (snd (snd (fst (reveal v))))))))));
    fold (tbs_rel (pm /. 2.0R) x.tbsCertificate.value (fst (reveal v)));
    fold (cert_flat pm x v);
    cert_pack ();
    elim_trade (arel true d_Certificate pm x v) (S.pts_to s #pm w);
    cert_out w v;
    r
  } else {
    with dk de. assert (A.pts_to key dk ** A.pts_to exp de);
    no_key_ok (KS.certificate_key w) dk de;
    no_key
  }
}
#pop-options

#push-options "--using_facts_from '* -ASN1 -LowParse -TLS13.Wire.Generated.X509 -TLS13.X509.Profile'"
let wrap_ok (c: B.bytes) (len: nat) (r: key_out) (dk de: B.bytes)
: Lemma (requires len <= B.length c /\ out_ok (KS.certificate_key (Seq.slice c 0 len)) r dk de)
        (ensures (let o = C.certificate_raw_public_key (CL.raw_slice c 0 len) in
                  let k = CL.raw_slice dk 0 (SZ.v r.n) in
                  SZ.v r.n <= B.length dk /\ SZ.v r.e <= B.length de /\
                  (r.kind == 1uy ==> o == Some (C.RawRsa k (CL.raw_slice de 0 (SZ.v r.e)))) /\
                  (r.kind == 2uy ==> o == Some (C.RawP256 k)) /\
                  (r.kind == 3uy ==> o == Some (C.RawP384 k))))
= TLS13.X509.KeySpec.Def.certificate_raw_public_key_def (Seq.slice c 0 len);
  assert (CL.raw_slice c 0 len == Seq.slice c 0 len);
  assert (CL.raw_slice dk 0 (SZ.v r.n) == Seq.slice dk 0 (SZ.v r.n));
  assert (CL.raw_slice de 0 (SZ.v r.e) == Seq.slice de 0 (SZ.v r.e));
  assert_norm (U8.v 1uy == 1 /\ U8.v 2uy == 2 /\ U8.v 3uy == 3)
#pop-options

(** The certificate's public key, copied out in the raw form the verifiers in
    [TLS13.Crypto] take: 1 for an RSA key (modulus in [key[0 .. lens[0])],
    exponent in [exponent[0 .. lens[1])]), 2 for a P-256 point and 3 for a
    P-384 point (in [key[0 .. lens[0])]), 0 for no usable key (including one too large for
    the buffers). *)
#push-options "--z3rlimit 80"
fn certificate_raw_public_key
  (certificate:array U8.t)
  (certificate_len:SZ.t)
  (key:array U8.t)
  (key_capacity:SZ.t)
  (exponent:array U8.t)
  (exponent_capacity:SZ.t)
  (lens:array SZ.t)
  requires pts_to certificate 'certificate_bytes **
           pts_to key 'old_key **
           pts_to exponent 'old_exponent **
           pts_to lens 'old_lens **
           pure (SZ.v certificate_len <= B.length 'certificate_bytes /\
                 B.length 'old_key == SZ.v key_capacity /\
                 B.length 'old_exponent == SZ.v exponent_capacity /\
                 Seq.length 'old_lens == 2)
  returns kind:U8.t
  ensures exists* key_bytes exponent_bytes lens_values.
          pts_to certificate 'certificate_bytes **
          pts_to key key_bytes **
          pts_to exponent exponent_bytes **
          pts_to lens lens_values **
          pure (B.length key_bytes == SZ.v key_capacity /\
                B.length exponent_bytes == SZ.v exponent_capacity /\
                Seq.length lens_values == 2 /\
                SZ.v (Seq.index lens_values 0) <= SZ.v key_capacity /\
                SZ.v (Seq.index lens_values 1) <= SZ.v exponent_capacity /\
                (kind == 1uy ==>
                  C.certificate_raw_public_key
                    (CL.raw_slice 'certificate_bytes 0 (SZ.v certificate_len)) ==
                  Some (C.RawRsa
                    (CL.raw_slice key_bytes 0 (SZ.v (Seq.index lens_values 0)))
                    (CL.raw_slice exponent_bytes 0 (SZ.v (Seq.index lens_values 1))))) /\
                (kind == 2uy ==>
                  C.certificate_raw_public_key
                    (CL.raw_slice 'certificate_bytes 0 (SZ.v certificate_len)) ==
                  Some (C.RawP256
                    (CL.raw_slice key_bytes 0 (SZ.v (Seq.index lens_values 0))))) /\
                (kind == 3uy ==>
                  C.certificate_raw_public_key
                    (CL.raw_slice 'certificate_bytes 0 (SZ.v certificate_len)) ==
                  Some (C.RawP384
                    (CL.raw_slice key_bytes 0 (SZ.v (Seq.index lens_values 0))))))
{
  A.pts_to_len lens;
  A.pts_to_len key;
  A.pts_to_len exponent;
  lens.(0sz) <- 0sz;
  lens.(1sz) <- 0sz;
  let s = ASN.prefix_slice certificate certificate_len;
  let r = cert_key s key key_capacity exponent exponent_capacity;
  elim_trade _ _;
  with dk de. assert (A.pts_to key dk ** A.pts_to exponent de);
  wrap_ok 'certificate_bytes (SZ.v certificate_len) r dk de;
  lens.(0sz) <- r.n;
  lens.(1sz) <- r.e;
  r.kind
}
#pop-options
