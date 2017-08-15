import galois.bitvec.join
import galois.bitvec.rotate

namespace crypto

section pair_list

  open list

  definition pair_list_aux {α β : Type} (z : α) (f : α → α → β) : option α → list α → list β
  | none     []       := []
  | (some x) []       := [f x z]
  | none     (x :: l) := pair_list_aux (some x) l
  | (some x) (a :: l) := f x a :: pair_list_aux none l

  definition pair_list {α β : Type} (z : α) (f : α → α → β) : list α → list β := pair_list_aux z f none

end pair_list

section common
  parameter (n : ℕ)
  parameters (s0 s1 : bitvec n → bitvec n)
  parameters (S0 S1 : bitvec n → bitvec n)
  parameters (cuberoots : list (bitvec n))

  /- 8n-bit hash, made up of eight n-bit words -/
  inductive hash : Type
  | mk : bitvec n → bitvec n → bitvec n → bitvec n → bitvec n → bitvec n → bitvec n → bitvec n → hash


  /- element-wise addition of two hash values -/
  definition hash_add : hash → hash → hash
  | (hash.mk x0 x1 x2 x3 x4 x5 x6 x7) (hash.mk y0 y1 y2 y3 y4 y5 y6 y7) :=
  hash.mk (bitvec.add x0 y0) (bitvec.add x1 y1) (bitvec.add x2 y2) (bitvec.add x3 y3)
          (bitvec.add x4 y4) (bitvec.add x5 y5) (bitvec.add x6 y6) (bitvec.add x7 y7)


  local notation `[` l:(foldr `, ` (h t, vector.cons h t) vector.nil `]`) := l

  /- concatenate the elements of a hash value into a single bitvector -/
  definition bitvec_of_hash : hash → bitvec (n * 8)
  | (hash.mk x0 x1 x2 x3 x4 x5 x6 x7) := bitvec.join ([x0,x1,x2,x3,x4,x5,x6,x7] : vector (bitvec n) 8)

  /- 16*n-bit chunk, made up of sixteen n-bit words -/
  inductive chunk : Type
  | mk : bitvec n → bitvec n → bitvec n → bitvec n → bitvec n → bitvec n → bitvec n → bitvec n →
         bitvec n → bitvec n → bitvec n → bitvec n → bitvec n → bitvec n → bitvec n → bitvec n → chunk

  definition chunk_hd : chunk → bitvec n
  | (chunk.mk w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15) := w0

  /- a single iteration of the expansion function -/
  definition expand1 : chunk → chunk
  | (chunk.mk w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15) :=
  let w16 := bitvec.add (bitvec.add (bitvec.add w0 (s0 w1)) w9) (s1 w14)
  in chunk.mk w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16

  open list

  /- expand a chunk into a message schedule -/
  definition expand : list (bitvec n) → chunk → list (bitvec n)
  | list.nil c := list.nil
  | (k :: l) c := list.cons (bitvec.add (chunk_hd c) k) (expand l (expand1 c))

  /- a single round of the compression function -/
  definition compress1 : bitvec n → hash → hash
  | kw (hash.mk a b c d e f g h) :=
  let ch    := bitvec.xor (bitvec.and e f) (bitvec.and (bitvec.not e) g),
      temp1 := bitvec.add (bitvec.add (bitvec.add h (S1 e)) ch) kw,
      maj   := bitvec.xor (bitvec.xor (bitvec.and a b) (bitvec.and a c)) (bitvec.and b c),
      temp2 := bitvec.add (S0 a) maj
  in hash.mk (bitvec.add temp1 temp2) a b c (bitvec.add d temp1) e f g

  /- hash a single expanded chunk -/
  definition hash1 : hash → list (bitvec n) → hash
  | h nil        := h
  | h (cons k l) := hash1 (compress1 k h) l

  /- expand and hash a list of chunks -/
  definition hash_chunks : hash → list chunk → hash
  | h nil        := h
  | h (cons c l) := hash_chunks (hash_add h (hash1 h (expand cuberoots c))) l

  /- type abbreviation -/
  definition pair : Type := bitvec n × bitvec n

  inductive chunk_part : Type
  | mk0 {} : chunk_part
  | mk1 : pair → chunk_part
  | mk2 : pair → pair → chunk_part
  | mk3 : pair → pair → pair → chunk_part
  | mk4 : pair → pair → pair → pair → chunk_part
  | mk5 : pair → pair → pair → pair → pair → chunk_part
  | mk6 : pair → pair → pair → pair → pair → pair → chunk_part
  | mk7 : pair → pair → pair → pair → pair → pair → pair → chunk_part

  definition pairs_to_chunk : pair → pair → pair → pair → pair → pair → pair → pair → chunk
  | (prod.mk a b) (prod.mk c d) (prod.mk e f) (prod.mk g h)
    (prod.mk i j) (prod.mk k l) (prod.mk m n) (prod.mk o p) :=
    chunk.mk a b c d e f g h i j k l m n o p

  definition z : pair := prod.mk 0 0

  /- first parameter is the 64-bit size to put at the end -/
  definition pairs_to_chunks_aux : pair → chunk_part → list pair → list chunk
  | s (chunk_part.mk0)               nil        := pairs_to_chunk z z z z z z z s :: nil
  | s (chunk_part.mk1 a)             nil        := pairs_to_chunk a z z z z z z s :: nil
  | s (chunk_part.mk2 a b)           nil        := pairs_to_chunk a b z z z z z s :: nil
  | s (chunk_part.mk3 a b c)         nil        := pairs_to_chunk a b c z z z z s :: nil
  | s (chunk_part.mk4 a b c d)       nil        := pairs_to_chunk a b c d z z z s :: nil
  | s (chunk_part.mk5 a b c d e)     nil        := pairs_to_chunk a b c d e z z s :: nil
  | s (chunk_part.mk6 a b c d e f)   nil        := pairs_to_chunk a b c d e f z s :: nil
  | s (chunk_part.mk7 a b c d e f g) nil        := pairs_to_chunk a b c d e f g s :: nil
  | s chunk_part.mk0                 (cons a l) := pairs_to_chunks_aux s (chunk_part.mk1 a) l
  | s (chunk_part.mk1 a)             (cons b l) := pairs_to_chunks_aux s (chunk_part.mk2 a b) l
  | s (chunk_part.mk2 a b)           (cons c l) := pairs_to_chunks_aux s (chunk_part.mk3 a b c) l
  | s (chunk_part.mk3 a b c)         (cons d l) := pairs_to_chunks_aux s (chunk_part.mk4 a b c d) l
  | s (chunk_part.mk4 a b c d)       (cons e l) := pairs_to_chunks_aux s (chunk_part.mk5 a b c d e) l
  | s (chunk_part.mk5 a b c d e)     (cons f l) := pairs_to_chunks_aux s (chunk_part.mk6 a b c d e f) l
  | s (chunk_part.mk6 a b c d e f)   (cons g l) := pairs_to_chunks_aux s (chunk_part.mk7 a b c d e f g) l
  | s (chunk_part.mk7 a b c d e f g) (cons h l) := pairs_to_chunk a b c d e f g h :: pairs_to_chunks_aux s chunk_part.mk0 l

  definition pairs_to_chunks : pair → list pair → list chunk
  | s := pairs_to_chunks_aux s chunk_part.mk0

  definition words_to_chunks : bitvec n → bitvec n → list (bitvec n) → list chunk
  | hi lo data := pairs_to_chunks (prod.mk hi lo) (pair_list 0 prod.mk data)

end common

namespace sha256

  /- first 32 bits of the fractional parts of the cube roots of the first 64 primes -/
  definition cuberoots : list (bitvec 32) :=
  [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
   0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
   0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
   0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
   0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
   0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
   0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
   0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

  definition hash0 : hash 32 :=
  hash.mk 0x6a09e667 0xbb67ae85 0x3c6ef372 0xa54ff53a
          0x510e527f 0x9b05688c 0x1f83d9ab 0x5be0cd19

  definition s0 : bitvec 32 → bitvec 32
  | x := bitvec.xor (bitvec.xor (bitvec.ror x 7) (bitvec.ror x 18)) (bitvec.ushr x 3)

  definition s1 : bitvec 32 → bitvec 32
  | x := bitvec.xor (bitvec.xor (bitvec.ror x 17) (bitvec.ror x 19)) (bitvec.ushr x 10)

  definition S0 : bitvec 32 → bitvec 32
  | x := bitvec.xor (bitvec.xor (bitvec.ror x 2) (bitvec.ror x 13)) (bitvec.ror x 22)

  definition S1 : bitvec 32 → bitvec 32
  | x := bitvec.xor (bitvec.xor (bitvec.ror x 6) (bitvec.ror x 11)) (bitvec.ror x 25)

  definition hash_chunks_32 := hash_chunks 32 s0 s1 S0 S1 cuberoots

  definition bytes_to_words : list (bitvec 8) → list (bitvec 32)
  | l := pair_list 0 bitvec.append (pair_list 0 bitvec.append l)

  definition preprocess (msg : list (bitvec 8)) : list (chunk 32) :=
  let len : bitvec 64 := list.foldl (λ n a, bitvec.add n 8) 0 msg,
      hi : bitvec 32 := vector.drop 32 (bitvec.ushr len 32),
      lo : bitvec 32 := vector.drop 32 len
  in words_to_chunks 32 hi lo (bytes_to_words (msg ++ [0x80]))

  definition sha256 (msg : list (bitvec 8)) : bitvec 256 :=
  bitvec_of_hash 32 (hash_chunks_32 hash0 (preprocess msg))

end sha256

namespace sha224

  /- The second 32 bits of the fractional parts of the square roots of the 9th through 16th primes 23..53 -/
  definition hash0 : hash 32 :=
  hash.mk 0xc1059ed8 0x367cd507 0x3070dd17 0xf70e5939
          0xffc00b31 0x68581511 0x64f98fa7 0xbefa4fa4

  definition sha224 (msg : list (bitvec 8)) : bitvec 224 :=
  vector.drop 32 (bitvec.ushr (bitvec_of_hash 32 (sha256.hash_chunks_32 hash0 (sha256.preprocess msg))) 32)
  /- should use "vector.firstn 224" but it fails to infer the less-than-or-equal constraint -/

end sha224

namespace sha512

  /- first 64 bits of the fractional parts of the cube roots of the first 80 primes -/
  definition cuberoots : list (bitvec 64) :=
  [0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
   0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
   0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
   0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
   0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
   0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
   0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
   0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
   0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
   0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
   0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
   0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
   0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
   0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
   0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
   0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
   0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
   0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
   0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
   0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817]

  definition hash0 : hash 64 :=
  hash.mk
    0x6a09e667f3bcc908
    0xbb67ae8584caa73b
    0x3c6ef372fe94f82b
    0xa54ff53a5f1d36f1
    0x510e527fade682d1
    0x9b05688c2b3e6c1f
    0x1f83d9abfb41bd6b
    0x5be0cd19137e2179

  definition s0 : bitvec 64 → bitvec 64
  | x := bitvec.xor (bitvec.xor (bitvec.ror x 1) (bitvec.ror x 8)) (bitvec.ushr x 7)

  definition s1 : bitvec 64 → bitvec 64
  | x := bitvec.xor (bitvec.xor (bitvec.ror x 19) (bitvec.ror x 61)) (bitvec.ushr x 6)

  definition S0 : bitvec 64 → bitvec 64
  | x := bitvec.xor (bitvec.xor (bitvec.ror x 28) (bitvec.ror x 34)) (bitvec.ror x 39)

  definition S1 : bitvec 64 → bitvec 64
  | x := bitvec.xor (bitvec.xor (bitvec.ror x 14) (bitvec.ror x 18)) (bitvec.ror x 41)

  definition hash_chunks_64 := hash_chunks 64 s0 s1 S0 S1 cuberoots

  definition bytes_to_words : list (bitvec 8) → list (bitvec 64)
  | l := pair_list 0 bitvec.append (pair_list 0 bitvec.append (pair_list 0 bitvec.append l))

  definition preprocess (msg : list (bitvec 8)) : list (chunk 64) :=
  let len : bitvec 128 := list.foldl (λ n a, bitvec.add n 8) 0 msg,
      hi : bitvec 64 := vector.drop 64 (bitvec.ushr len 64),
      lo : bitvec 64 := vector.drop 64 len
  in words_to_chunks 64 hi lo (bytes_to_words (msg ++ [0x80]))

  definition sha512 (msg : list (bitvec 8)) : bitvec 512 :=
  bitvec_of_hash 64 (hash_chunks_64 hash0 (preprocess msg))

end sha512

namespace sha384

  definition hash0 : hash 64 :=
  hash.mk 0xcbbb9d5dc1059ed8 0x629a292a367cd507 0x9159015a3070dd17 0x152fecd8f70e5939
          0x67332667ffc00b31 0x8eb44a8768581511 0xdb0c2e0d64f98fa7 0x47b5481dbefa4fa4

  definition sha384 (msg : list (bitvec 8)) : bitvec 384 :=
  vector.drop 128 (bitvec.ushr (bitvec_of_hash 64 (sha512.hash_chunks_64 hash0 (sha512.preprocess msg))) 128)
  /- should use "vector.firstn 384" but it fails to infer the less-than-or-equal constraint -/

end sha384

namespace sha512_224

  definition hash0 : hash 64 :=
  hash.mk 0x8c3d37c819544da2 0x73e1996689dcd4d6 0x1dfab7ae32ff9c82 0x679dd514582f9fcf
          0x0f6d2b697bd44da8 0x77e36f7304c48942 0x3f9d85a86a1d36c8 0x1112e6ad91d692a1

  definition sha512_224 (msg : list (bitvec 8)) : bitvec 224 :=
  vector.drop 288 (bitvec.ushr (bitvec_of_hash 64 (sha512.hash_chunks_64 hash0 (sha512.preprocess msg))) 288)
  /- should use "vector.firstn 288" but it fails to infer the less-than-or-equal constraint -/

end sha512_224

namespace sha512_256

  definition hash0 : hash 64 :=
  hash.mk 0x22312194fc2bf72c 0x9f555fa3c84c64c2 0x2393b86b6f53b151 0x963877195940eabd
          0x96283ee2a88effe3 0xbe5e1e2553863992 0x2b0199fc2c85b8aa 0x0eb72ddc81c52ca2

  definition sha512_256 (msg : list (bitvec 8)) : bitvec 256 :=
  vector.take 256 (bitvec_of_hash 64 (sha512.hash_chunks_64 hash0 (sha512.preprocess msg)))

end sha512_256


definition sha224 : list (bitvec 8) → bitvec 224 := sha224.sha224
definition sha256 : list (bitvec 8) → bitvec 256 := sha256.sha256
definition sha384 : list (bitvec 8) → bitvec 384 := sha384.sha384
definition sha512 : list (bitvec 8) → bitvec 512 := sha512.sha512

definition sha512_224 : list (bitvec 8) → bitvec 224 := sha512_224.sha512_224
definition sha512_256 : list (bitvec 8) → bitvec 256 := sha512_256.sha512_256

end crypto
