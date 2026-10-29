module TLS13.Pem.Spec

(** The PEM front end (RFC 7468) that turns the textual credentials a host
    supplies into the DER the verified client and server consume:

    - [certificates_to_der] concatenates the DER of every
      "-----BEGIN CERTIFICATE-----" block of a bundle, which is the trust-store
      form [TLS13.X509.Spec] reads;
    - [private_key_to_der] passes DER through unchanged and otherwise decodes
      the first "-----BEGIN ...PRIVATE KEY-----" block, which is the form
      [TLS13.Impl.ServerCredentials] reads.

    Block bodies are base64 (RFC 4648 section 4).  Whitespace inside a body is
    skipped and '=' padding is accepted only at the end; the decoder is lenient
    about the amount of padding, as PEM readers usually are, but rejects any
    other character and a dangling 6-bit group.  [TLS13.Impl.Pem] implements
    these functions. *)

module B = TLS13.Bytes
module Seq = FStar.Seq
module U8 = FStar.UInt8

(** ** Byte-string search *)

(** [a[ai, ai+n)] equals [b[bi, bi+n)]. *)
let rec region_eq
  (a:B.bytes) (ai:nat) (b:B.bytes) (bi:nat)
  (n:nat{ai + n <= Seq.length a /\ bi + n <= Seq.length b})
  : Tot bool (decreases n)
  = n = 0 ||
    (Seq.index a ai = Seq.index b bi && region_eq a (ai + 1) b (bi + 1) (n - 1))

let matches_at (h:B.bytes) (i:nat) (needle:B.bytes) : bool =
  i + Seq.length needle <= Seq.length h &&
  region_eq h i needle 0 (Seq.length needle)

(** The first occurrence of [needle] in [h] at or after [from]. *)
let rec find_from (h needle:B.bytes) (from:nat)
  : Tot (option (i:nat{from <= i /\ i + Seq.length needle <= Seq.length h}))
        (decreases (Seq.length h + 1 - from))
  = if from + Seq.length needle > Seq.length h then None
    else if matches_at h from needle then Some from
    else match find_from h needle (from + 1) with
         | Some i -> Some i
         | None -> None

(** The first occurrence of byte [c] in [h] at or after [from]. *)
let rec find_byte (h:B.bytes) (c:U8.t) (from:nat{from <= Seq.length h})
  : Tot (option (i:nat{from <= i /\ i < Seq.length h}))
        (decreases (Seq.length h - from))
  = if from = Seq.length h then None
    else if Seq.index h from = c then Some from
    else match find_byte h c (from + 1) with
         | Some i -> Some i
         | None -> None

(** [hi] moved left past any '\r' bytes, but not past [lo]. *)
let rec strip_cr (h:B.bytes) (lo:nat) (hi:nat{lo <= hi /\ hi <= Seq.length h})
  : Tot (r:nat{lo <= r /\ r <= hi}) (decreases hi)
  = if hi > lo && Seq.index h (hi - 1) = 13uy then strip_cr h lo (hi - 1) else hi

(** ** Base64 *)

let is_whitespace (c:U8.t) : bool =
  c = 32uy || c = 9uy || c = 13uy || c = 10uy

let pad_char : U8.t = 61uy

(** The 6-bit value of a base64 alphabet character. *)
let b64_value (c:U8.t) : option (v:U8.t{U8.v v < 64}) =
  if U8.gte c 65uy && U8.lte c 90uy then Some (U8.sub c 65uy)        (* A-Z *)
  else if U8.gte c 97uy && U8.lte c 122uy then Some (U8.sub c 71uy)  (* a-z *)
  else if U8.gte c 48uy && U8.lte c 57uy then Some (U8.add c 4uy)    (* 0-9 *)
  else if c = 43uy then Some 62uy                                     (* +   *)
  else if c = 47uy then Some 63uy                                     (* /   *)
  else None

(** Decodes [s[i..]] given the decoder state: [acc] holds the [bits]
    not-yet-emitted low bits, [pad] counts the '=' seen and [out] is the
    output so far. *)
let rec b64_go
  (s:B.bytes) (i:nat{i <= Seq.length s}) (acc bits pad:nat) (out:B.bytes)
  : Tot (option B.bytes) (decreases (Seq.length s - i))
  = if i = Seq.length s then
      (if pad > 2 || bits >= 6 then None else Some out)
    else
      let c = Seq.index s i in
      if is_whitespace c then b64_go s (i + 1) acc bits pad out
      else if c = pad_char then b64_go s (i + 1) acc bits (pad + 1) out
      else match b64_value c with
        | None -> None
        | Some v ->
          if pad <> 0 then None
          else
            let acc' = acc * 64 + U8.v v in
            let bits' = bits + 6 in
            if bits' >= 8 then
              let d = pow2 (bits' - 8) in
              b64_go s (i + 1) (acc' % d) (bits' - 8) pad
                (Seq.snoc out (U8.uint_to_t ((acc' / d) % 256)))
            else b64_go s (i + 1) acc' bits' pad out

let b64_decode (s:B.bytes) : option B.bytes = b64_go s 0 0 0 0 Seq.empty

(** A decoded PEM block body: valid, non-empty base64. *)
let decode_body (h:B.bytes) (lo:nat) (hi:nat{lo <= hi /\ hi <= Seq.length h})
  : option B.bytes
  = match b64_decode (Seq.slice h lo hi) with
    | Some d -> if Seq.length d = 0 then None else Some d
    | None -> None

(** ** Certificates *)

(** "-----BEGIN CERTIFICATE-----" *)
let cert_begin : B.bytes = B.of_list [
  45uy; 45uy; 45uy; 45uy; 45uy; 66uy; 69uy; 71uy; 73uy; 78uy; 32uy;
  67uy; 69uy; 82uy; 84uy; 73uy; 70uy; 73uy; 67uy; 65uy; 84uy; 69uy;
  45uy; 45uy; 45uy; 45uy; 45uy]

noextract
let cert_begin_list : list U8.t = [45uy; 45uy; 45uy; 45uy; 45uy; 66uy; 69uy; 71uy; 73uy; 78uy; 32uy; 67uy; 69uy; 82uy; 84uy; 73uy; 70uy; 73uy; 67uy; 65uy; 84uy; 69uy; 45uy; 45uy; 45uy; 45uy; 45uy]

(** The bytes of [cert_begin], stated explicitly for implementations that
    write the needle one byte at a time. *)
let cert_begin_bytes ()
  : Lemma
    (Seq.length cert_begin == 27 /\
     Seq.index cert_begin 0 == 45uy /\
     Seq.index cert_begin 1 == 45uy /\
     Seq.index cert_begin 2 == 45uy /\
     Seq.index cert_begin 3 == 45uy /\
     Seq.index cert_begin 4 == 45uy /\
     Seq.index cert_begin 5 == 66uy /\
     Seq.index cert_begin 6 == 69uy /\
     Seq.index cert_begin 7 == 71uy /\
     Seq.index cert_begin 8 == 73uy /\
     Seq.index cert_begin 9 == 78uy /\
     Seq.index cert_begin 10 == 32uy /\
     Seq.index cert_begin 11 == 67uy /\
     Seq.index cert_begin 12 == 69uy /\
     Seq.index cert_begin 13 == 82uy /\
     Seq.index cert_begin 14 == 84uy /\
     Seq.index cert_begin 15 == 73uy /\
     Seq.index cert_begin 16 == 70uy /\
     Seq.index cert_begin 17 == 73uy /\
     Seq.index cert_begin 18 == 67uy /\
     Seq.index cert_begin 19 == 65uy /\
     Seq.index cert_begin 20 == 84uy /\
     Seq.index cert_begin 21 == 69uy /\
     Seq.index cert_begin 22 == 45uy /\
     Seq.index cert_begin 23 == 45uy /\
     Seq.index cert_begin 24 == 45uy /\
     Seq.index cert_begin 25 == 45uy /\
     Seq.index cert_begin 26 == 45uy)
  = assert_norm (cert_begin == B.of_list cert_begin_list);
    assert_norm (List.Tot.length cert_begin_list == 27);
    Seq.lemma_seq_of_list_index cert_begin_list 0; assert_norm (List.Tot.index cert_begin_list 0 == 45uy);
    Seq.lemma_seq_of_list_index cert_begin_list 1; assert_norm (List.Tot.index cert_begin_list 1 == 45uy);
    Seq.lemma_seq_of_list_index cert_begin_list 2; assert_norm (List.Tot.index cert_begin_list 2 == 45uy);
    Seq.lemma_seq_of_list_index cert_begin_list 3; assert_norm (List.Tot.index cert_begin_list 3 == 45uy);
    Seq.lemma_seq_of_list_index cert_begin_list 4; assert_norm (List.Tot.index cert_begin_list 4 == 45uy);
    Seq.lemma_seq_of_list_index cert_begin_list 5; assert_norm (List.Tot.index cert_begin_list 5 == 66uy);
    Seq.lemma_seq_of_list_index cert_begin_list 6; assert_norm (List.Tot.index cert_begin_list 6 == 69uy);
    Seq.lemma_seq_of_list_index cert_begin_list 7; assert_norm (List.Tot.index cert_begin_list 7 == 71uy);
    Seq.lemma_seq_of_list_index cert_begin_list 8; assert_norm (List.Tot.index cert_begin_list 8 == 73uy);
    Seq.lemma_seq_of_list_index cert_begin_list 9; assert_norm (List.Tot.index cert_begin_list 9 == 78uy);
    Seq.lemma_seq_of_list_index cert_begin_list 10; assert_norm (List.Tot.index cert_begin_list 10 == 32uy);
    Seq.lemma_seq_of_list_index cert_begin_list 11; assert_norm (List.Tot.index cert_begin_list 11 == 67uy);
    Seq.lemma_seq_of_list_index cert_begin_list 12; assert_norm (List.Tot.index cert_begin_list 12 == 69uy);
    Seq.lemma_seq_of_list_index cert_begin_list 13; assert_norm (List.Tot.index cert_begin_list 13 == 82uy);
    Seq.lemma_seq_of_list_index cert_begin_list 14; assert_norm (List.Tot.index cert_begin_list 14 == 84uy);
    Seq.lemma_seq_of_list_index cert_begin_list 15; assert_norm (List.Tot.index cert_begin_list 15 == 73uy);
    Seq.lemma_seq_of_list_index cert_begin_list 16; assert_norm (List.Tot.index cert_begin_list 16 == 70uy);
    Seq.lemma_seq_of_list_index cert_begin_list 17; assert_norm (List.Tot.index cert_begin_list 17 == 73uy);
    Seq.lemma_seq_of_list_index cert_begin_list 18; assert_norm (List.Tot.index cert_begin_list 18 == 67uy);
    Seq.lemma_seq_of_list_index cert_begin_list 19; assert_norm (List.Tot.index cert_begin_list 19 == 65uy);
    Seq.lemma_seq_of_list_index cert_begin_list 20; assert_norm (List.Tot.index cert_begin_list 20 == 84uy);
    Seq.lemma_seq_of_list_index cert_begin_list 21; assert_norm (List.Tot.index cert_begin_list 21 == 69uy);
    Seq.lemma_seq_of_list_index cert_begin_list 22; assert_norm (List.Tot.index cert_begin_list 22 == 45uy);
    Seq.lemma_seq_of_list_index cert_begin_list 23; assert_norm (List.Tot.index cert_begin_list 23 == 45uy);
    Seq.lemma_seq_of_list_index cert_begin_list 24; assert_norm (List.Tot.index cert_begin_list 24 == 45uy);
    Seq.lemma_seq_of_list_index cert_begin_list 25; assert_norm (List.Tot.index cert_begin_list 25 == 45uy);
    Seq.lemma_seq_of_list_index cert_begin_list 26; assert_norm (List.Tot.index cert_begin_list 26 == 45uy)


(** "-----END CERTIFICATE-----" *)
let cert_end : B.bytes = B.of_list [
  45uy; 45uy; 45uy; 45uy; 45uy; 69uy; 78uy; 68uy; 32uy;
  67uy; 69uy; 82uy; 84uy; 73uy; 70uy; 73uy; 67uy; 65uy; 84uy; 69uy;
  45uy; 45uy; 45uy; 45uy; 45uy]

noextract
let cert_end_list : list U8.t = [45uy; 45uy; 45uy; 45uy; 45uy; 69uy; 78uy; 68uy; 32uy; 67uy; 69uy; 82uy; 84uy; 73uy; 70uy; 73uy; 67uy; 65uy; 84uy; 69uy; 45uy; 45uy; 45uy; 45uy; 45uy]

(** The bytes of [cert_end], stated explicitly for implementations that
    write the needle one byte at a time. *)
let cert_end_bytes ()
  : Lemma
    (Seq.length cert_end == 25 /\
     Seq.index cert_end 0 == 45uy /\
     Seq.index cert_end 1 == 45uy /\
     Seq.index cert_end 2 == 45uy /\
     Seq.index cert_end 3 == 45uy /\
     Seq.index cert_end 4 == 45uy /\
     Seq.index cert_end 5 == 69uy /\
     Seq.index cert_end 6 == 78uy /\
     Seq.index cert_end 7 == 68uy /\
     Seq.index cert_end 8 == 32uy /\
     Seq.index cert_end 9 == 67uy /\
     Seq.index cert_end 10 == 69uy /\
     Seq.index cert_end 11 == 82uy /\
     Seq.index cert_end 12 == 84uy /\
     Seq.index cert_end 13 == 73uy /\
     Seq.index cert_end 14 == 70uy /\
     Seq.index cert_end 15 == 73uy /\
     Seq.index cert_end 16 == 67uy /\
     Seq.index cert_end 17 == 65uy /\
     Seq.index cert_end 18 == 84uy /\
     Seq.index cert_end 19 == 69uy /\
     Seq.index cert_end 20 == 45uy /\
     Seq.index cert_end 21 == 45uy /\
     Seq.index cert_end 22 == 45uy /\
     Seq.index cert_end 23 == 45uy /\
     Seq.index cert_end 24 == 45uy)
  = assert_norm (cert_end == B.of_list cert_end_list);
    assert_norm (List.Tot.length cert_end_list == 25);
    Seq.lemma_seq_of_list_index cert_end_list 0; assert_norm (List.Tot.index cert_end_list 0 == 45uy);
    Seq.lemma_seq_of_list_index cert_end_list 1; assert_norm (List.Tot.index cert_end_list 1 == 45uy);
    Seq.lemma_seq_of_list_index cert_end_list 2; assert_norm (List.Tot.index cert_end_list 2 == 45uy);
    Seq.lemma_seq_of_list_index cert_end_list 3; assert_norm (List.Tot.index cert_end_list 3 == 45uy);
    Seq.lemma_seq_of_list_index cert_end_list 4; assert_norm (List.Tot.index cert_end_list 4 == 45uy);
    Seq.lemma_seq_of_list_index cert_end_list 5; assert_norm (List.Tot.index cert_end_list 5 == 69uy);
    Seq.lemma_seq_of_list_index cert_end_list 6; assert_norm (List.Tot.index cert_end_list 6 == 78uy);
    Seq.lemma_seq_of_list_index cert_end_list 7; assert_norm (List.Tot.index cert_end_list 7 == 68uy);
    Seq.lemma_seq_of_list_index cert_end_list 8; assert_norm (List.Tot.index cert_end_list 8 == 32uy);
    Seq.lemma_seq_of_list_index cert_end_list 9; assert_norm (List.Tot.index cert_end_list 9 == 67uy);
    Seq.lemma_seq_of_list_index cert_end_list 10; assert_norm (List.Tot.index cert_end_list 10 == 69uy);
    Seq.lemma_seq_of_list_index cert_end_list 11; assert_norm (List.Tot.index cert_end_list 11 == 82uy);
    Seq.lemma_seq_of_list_index cert_end_list 12; assert_norm (List.Tot.index cert_end_list 12 == 84uy);
    Seq.lemma_seq_of_list_index cert_end_list 13; assert_norm (List.Tot.index cert_end_list 13 == 73uy);
    Seq.lemma_seq_of_list_index cert_end_list 14; assert_norm (List.Tot.index cert_end_list 14 == 70uy);
    Seq.lemma_seq_of_list_index cert_end_list 15; assert_norm (List.Tot.index cert_end_list 15 == 73uy);
    Seq.lemma_seq_of_list_index cert_end_list 16; assert_norm (List.Tot.index cert_end_list 16 == 67uy);
    Seq.lemma_seq_of_list_index cert_end_list 17; assert_norm (List.Tot.index cert_end_list 17 == 65uy);
    Seq.lemma_seq_of_list_index cert_end_list 18; assert_norm (List.Tot.index cert_end_list 18 == 84uy);
    Seq.lemma_seq_of_list_index cert_end_list 19; assert_norm (List.Tot.index cert_end_list 19 == 69uy);
    Seq.lemma_seq_of_list_index cert_end_list 20; assert_norm (List.Tot.index cert_end_list 20 == 45uy);
    Seq.lemma_seq_of_list_index cert_end_list 21; assert_norm (List.Tot.index cert_end_list 21 == 45uy);
    Seq.lemma_seq_of_list_index cert_end_list 22; assert_norm (List.Tot.index cert_end_list 22 == 45uy);
    Seq.lemma_seq_of_list_index cert_end_list 23; assert_norm (List.Tot.index cert_end_list 23 == 45uy);
    Seq.lemma_seq_of_list_index cert_end_list 24; assert_norm (List.Tot.index cert_end_list 24 == 45uy)


let rec certificates_go
  (pem:B.bytes) (cursor:nat{cursor <= Seq.length pem}) (der:B.bytes) (found:bool)
  : Tot (option B.bytes) (decreases (Seq.length pem - cursor))
  = match find_from pem cert_begin cursor with
    | None -> if Seq.length pem <> 0 && not found then None else Some der
    | Some b ->
      let body = b + Seq.length cert_begin in
      match find_from pem cert_end body with
      | None -> None
      | Some e ->
        match decode_body pem body e with
        | None -> None
        | Some d ->
          certificates_go pem (e + Seq.length cert_end) (Seq.append der d) true

(** The concatenated DER of every CERTIFICATE block of [pem], in order.  An
    empty input yields an empty result; a non-empty input without any
    certificate, or with a malformed one, is rejected.  Text outside the
    blocks is ignored. *)
let certificates_to_der (pem:B.bytes) : option B.bytes =
  certificates_go pem 0 Seq.empty false

(** ** Private keys *)

(** "-----BEGIN " *)
let key_begin : B.bytes = B.of_list [
  45uy; 45uy; 45uy; 45uy; 45uy; 66uy; 69uy; 71uy; 73uy; 78uy; 32uy]

noextract
let key_begin_list : list U8.t = [45uy; 45uy; 45uy; 45uy; 45uy; 66uy; 69uy; 71uy; 73uy; 78uy; 32uy]

(** The bytes of [key_begin], stated explicitly for implementations that
    write the needle one byte at a time. *)
let key_begin_bytes ()
  : Lemma
    (Seq.length key_begin == 11 /\
     Seq.index key_begin 0 == 45uy /\
     Seq.index key_begin 1 == 45uy /\
     Seq.index key_begin 2 == 45uy /\
     Seq.index key_begin 3 == 45uy /\
     Seq.index key_begin 4 == 45uy /\
     Seq.index key_begin 5 == 66uy /\
     Seq.index key_begin 6 == 69uy /\
     Seq.index key_begin 7 == 71uy /\
     Seq.index key_begin 8 == 73uy /\
     Seq.index key_begin 9 == 78uy /\
     Seq.index key_begin 10 == 32uy)
  = assert_norm (key_begin == B.of_list key_begin_list);
    assert_norm (List.Tot.length key_begin_list == 11);
    Seq.lemma_seq_of_list_index key_begin_list 0; assert_norm (List.Tot.index key_begin_list 0 == 45uy);
    Seq.lemma_seq_of_list_index key_begin_list 1; assert_norm (List.Tot.index key_begin_list 1 == 45uy);
    Seq.lemma_seq_of_list_index key_begin_list 2; assert_norm (List.Tot.index key_begin_list 2 == 45uy);
    Seq.lemma_seq_of_list_index key_begin_list 3; assert_norm (List.Tot.index key_begin_list 3 == 45uy);
    Seq.lemma_seq_of_list_index key_begin_list 4; assert_norm (List.Tot.index key_begin_list 4 == 45uy);
    Seq.lemma_seq_of_list_index key_begin_list 5; assert_norm (List.Tot.index key_begin_list 5 == 66uy);
    Seq.lemma_seq_of_list_index key_begin_list 6; assert_norm (List.Tot.index key_begin_list 6 == 69uy);
    Seq.lemma_seq_of_list_index key_begin_list 7; assert_norm (List.Tot.index key_begin_list 7 == 71uy);
    Seq.lemma_seq_of_list_index key_begin_list 8; assert_norm (List.Tot.index key_begin_list 8 == 73uy);
    Seq.lemma_seq_of_list_index key_begin_list 9; assert_norm (List.Tot.index key_begin_list 9 == 78uy);
    Seq.lemma_seq_of_list_index key_begin_list 10; assert_norm (List.Tot.index key_begin_list 10 == 32uy)


(** "PRIVATE KEY-----" *)
let key_suffix : B.bytes = B.of_list [
  80uy; 82uy; 73uy; 86uy; 65uy; 84uy; 69uy; 32uy; 75uy; 69uy; 89uy;
  45uy; 45uy; 45uy; 45uy; 45uy]

noextract
let key_suffix_list : list U8.t = [80uy; 82uy; 73uy; 86uy; 65uy; 84uy; 69uy; 32uy; 75uy; 69uy; 89uy; 45uy; 45uy; 45uy; 45uy; 45uy]

(** The bytes of [key_suffix], stated explicitly for implementations that
    write the needle one byte at a time. *)
let key_suffix_bytes ()
  : Lemma
    (Seq.length key_suffix == 16 /\
     Seq.index key_suffix 0 == 80uy /\
     Seq.index key_suffix 1 == 82uy /\
     Seq.index key_suffix 2 == 73uy /\
     Seq.index key_suffix 3 == 86uy /\
     Seq.index key_suffix 4 == 65uy /\
     Seq.index key_suffix 5 == 84uy /\
     Seq.index key_suffix 6 == 69uy /\
     Seq.index key_suffix 7 == 32uy /\
     Seq.index key_suffix 8 == 75uy /\
     Seq.index key_suffix 9 == 69uy /\
     Seq.index key_suffix 10 == 89uy /\
     Seq.index key_suffix 11 == 45uy /\
     Seq.index key_suffix 12 == 45uy /\
     Seq.index key_suffix 13 == 45uy /\
     Seq.index key_suffix 14 == 45uy /\
     Seq.index key_suffix 15 == 45uy)
  = assert_norm (key_suffix == B.of_list key_suffix_list);
    assert_norm (List.Tot.length key_suffix_list == 16);
    Seq.lemma_seq_of_list_index key_suffix_list 0; assert_norm (List.Tot.index key_suffix_list 0 == 80uy);
    Seq.lemma_seq_of_list_index key_suffix_list 1; assert_norm (List.Tot.index key_suffix_list 1 == 82uy);
    Seq.lemma_seq_of_list_index key_suffix_list 2; assert_norm (List.Tot.index key_suffix_list 2 == 73uy);
    Seq.lemma_seq_of_list_index key_suffix_list 3; assert_norm (List.Tot.index key_suffix_list 3 == 86uy);
    Seq.lemma_seq_of_list_index key_suffix_list 4; assert_norm (List.Tot.index key_suffix_list 4 == 65uy);
    Seq.lemma_seq_of_list_index key_suffix_list 5; assert_norm (List.Tot.index key_suffix_list 5 == 84uy);
    Seq.lemma_seq_of_list_index key_suffix_list 6; assert_norm (List.Tot.index key_suffix_list 6 == 69uy);
    Seq.lemma_seq_of_list_index key_suffix_list 7; assert_norm (List.Tot.index key_suffix_list 7 == 32uy);
    Seq.lemma_seq_of_list_index key_suffix_list 8; assert_norm (List.Tot.index key_suffix_list 8 == 75uy);
    Seq.lemma_seq_of_list_index key_suffix_list 9; assert_norm (List.Tot.index key_suffix_list 9 == 69uy);
    Seq.lemma_seq_of_list_index key_suffix_list 10; assert_norm (List.Tot.index key_suffix_list 10 == 89uy);
    Seq.lemma_seq_of_list_index key_suffix_list 11; assert_norm (List.Tot.index key_suffix_list 11 == 45uy);
    Seq.lemma_seq_of_list_index key_suffix_list 12; assert_norm (List.Tot.index key_suffix_list 12 == 45uy);
    Seq.lemma_seq_of_list_index key_suffix_list 13; assert_norm (List.Tot.index key_suffix_list 13 == 45uy);
    Seq.lemma_seq_of_list_index key_suffix_list 14; assert_norm (List.Tot.index key_suffix_list 14 == 45uy);
    Seq.lemma_seq_of_list_index key_suffix_list 15; assert_norm (List.Tot.index key_suffix_list 15 == 45uy)


(** "-----END " *)
let key_end : B.bytes = B.of_list [
  45uy; 45uy; 45uy; 45uy; 45uy; 69uy; 78uy; 68uy; 32uy]

noextract
let key_end_list : list U8.t = [45uy; 45uy; 45uy; 45uy; 45uy; 69uy; 78uy; 68uy; 32uy]

(** The bytes of [key_end], stated explicitly for implementations that
    write the needle one byte at a time. *)
let key_end_bytes ()
  : Lemma
    (Seq.length key_end == 9 /\
     Seq.index key_end 0 == 45uy /\
     Seq.index key_end 1 == 45uy /\
     Seq.index key_end 2 == 45uy /\
     Seq.index key_end 3 == 45uy /\
     Seq.index key_end 4 == 45uy /\
     Seq.index key_end 5 == 69uy /\
     Seq.index key_end 6 == 78uy /\
     Seq.index key_end 7 == 68uy /\
     Seq.index key_end 8 == 32uy)
  = assert_norm (key_end == B.of_list key_end_list);
    assert_norm (List.Tot.length key_end_list == 9);
    Seq.lemma_seq_of_list_index key_end_list 0; assert_norm (List.Tot.index key_end_list 0 == 45uy);
    Seq.lemma_seq_of_list_index key_end_list 1; assert_norm (List.Tot.index key_end_list 1 == 45uy);
    Seq.lemma_seq_of_list_index key_end_list 2; assert_norm (List.Tot.index key_end_list 2 == 45uy);
    Seq.lemma_seq_of_list_index key_end_list 3; assert_norm (List.Tot.index key_end_list 3 == 45uy);
    Seq.lemma_seq_of_list_index key_end_list 4; assert_norm (List.Tot.index key_end_list 4 == 45uy);
    Seq.lemma_seq_of_list_index key_end_list 5; assert_norm (List.Tot.index key_end_list 5 == 69uy);
    Seq.lemma_seq_of_list_index key_end_list 6; assert_norm (List.Tot.index key_end_list 6 == 78uy);
    Seq.lemma_seq_of_list_index key_end_list 7; assert_norm (List.Tot.index key_end_list 7 == 68uy);
    Seq.lemma_seq_of_list_index key_end_list 8; assert_norm (List.Tot.index key_end_list 8 == 32uy)


(** Scans [key] from [cursor] for a "-----BEGIN <label>" line whose label
    ends in "PRIVATE KEY-----" (ignoring a trailing '\r'), and decodes its
    body up to the matching "-----END <label>".  Other blocks, such as
    "EC PARAMETERS", are skipped. *)
let rec private_key_go (key:B.bytes) (cursor:nat{cursor <= Seq.length key})
  : Tot (option B.bytes) (decreases (Seq.length key - cursor))
  = match find_from key key_begin cursor with
    | None -> None
    | Some b ->
      let label = b + Seq.length key_begin in
      let eol = find_byte key 10uy label in
      let line_end =
        strip_cr key label (match eol with Some e -> e | None -> Seq.length key) in
      if Some? eol &&
         line_end - label >= Seq.length key_suffix &&
         matches_at key (line_end - Seq.length key_suffix) key_suffix
      then
        let body = Some?.v eol + 1 in
        match find_from key (Seq.append key_end (Seq.slice key label line_end)) body with
        | None -> None
        | Some f -> decode_body key body f
      else private_key_go key label

(** A private key as DER: input that starts with a DER SEQUENCE tag is
    returned unchanged; otherwise the first PEM private-key block (PKCS#8
    "PRIVATE KEY", PKCS#1 "RSA PRIVATE KEY" or SEC1 "EC PRIVATE KEY") is
    decoded. *)
let private_key_to_der (key:B.bytes) : option B.bytes =
  if Seq.length key = 0 then None
  else if Seq.index key 0 = 0x30uy then Some key
  else private_key_go key 0

(** ** Properties *)

let rec region_eq_iff
  (a:B.bytes) (ai:nat) (b:B.bytes) (bi:nat)
  (n:nat{ai + n <= Seq.length a /\ bi + n <= Seq.length b})
  : Lemma (ensures region_eq a ai b bi n <==>
                   (forall (k:nat). k < n ==> Seq.index a (ai + k) == Seq.index b (bi + k)))
          (decreases n)
  = if n = 0 then ()
    else begin
      region_eq_iff a (ai + 1) b (bi + 1) (n - 1);
      let q (k:nat) : prop = k < n ==> Seq.index a (ai + k) == Seq.index b (bi + k) in
      let r (k:nat) : prop =
        k < n - 1 ==> Seq.index a (ai + 1 + k) == Seq.index b (bi + 1 + k) in
      introduce (forall (k:nat). q k) ==> (Seq.index a ai == Seq.index b bi /\ (forall (k:nat). r k))
      with begin
        eliminate forall (k:nat). q k with 0;
        introduce forall (k:nat). r k
        with eliminate forall (k:nat). q k with (k + 1)
      end;
      introduce (Seq.index a ai == Seq.index b bi /\ (forall (k:nat). r k)) ==> (forall (k:nat). q k)
      with introduce forall (k:nat). q k
      with (if k = 0 then () else eliminate forall (k:nat). r k with (k - 1))
    end

(** [matches_at] is substring equality. *)
let matches_at_iff (h:B.bytes) (i:nat) (needle:B.bytes)
  : Lemma (matches_at h i needle <==>
           (i + Seq.length needle <= Seq.length h /\
            Seq.slice h i (i + Seq.length needle) == needle))
  = if i + Seq.length needle <= Seq.length h then begin
      region_eq_iff h i needle 0 (Seq.length needle);
      let sl = Seq.slice h i (i + Seq.length needle) in
      if matches_at h i needle then Seq.lemma_eq_intro sl needle
      else
        introduce sl == needle ==> False
        with assert (forall (k:nat). k < Seq.length needle ==>
                       Seq.index sl k == Seq.index needle k)
    end

(** [find_from] finds the first occurrence. *)
let rec find_from_first (h needle:B.bytes) (from:nat)
  : Lemma (ensures (match find_from h needle from with
                    | Some i -> matches_at h i needle /\
                               (forall (j:nat). from <= j /\ j < i ==> not (matches_at h j needle))
                    | None -> forall (j:nat). from <= j ==> not (matches_at h j needle)))
          (decreases (Seq.length h + 1 - from))
  = if from + Seq.length needle > Seq.length h then ()
    else if matches_at h from needle then ()
    else find_from_first h needle (from + 1)
