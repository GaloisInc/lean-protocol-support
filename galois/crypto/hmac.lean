/- This defines an hmac primitive.
 -/
import galois.word
import galois.tactic.nat
import galois.bitvec.join
import galois.crypto.sha2

namespace crypto

definition hmac {olen : ℕ} -- ^ Output length
                (blen : ℕ) -- ^ Block length
                (hash : list byte → vector byte olen)
                (key : list byte)
                (msg : list byte)
                : vector byte olen :=
  let klen := list.length key in
  let padded_key :=
        if blen ≥ klen then
          key ++ list.repeat 0 (blen - klen)
        else
          key ++ list.repeat 0 (blen - olen) in
  let ki := list.map (bitvec.xor 54) padded_key in
  let ko := list.map (bitvec.xor 92) padded_key in
  hash (ko ++ (hash (ki ++ msg))^.to_list)

end crypto

namespace hmac

/- hash_algorithm -/

inductive hash_algorithm
  | sha1      : hash_algorithm
  | sha2_256  : hash_algorithm
  | ripemd160 : hash_algorithm
  | sha2_224  : hash_algorithm
  | sha2_384  : hash_algorithm
  | sha2_512  : hash_algorithm
  | sha3_224  : hash_algorithm
  | sha3_256  : hash_algorithm
  | sha3_384  : hash_algorithm
  | sha3_512  : hash_algorithm
  | sm3       : hash_algorithm

namespace hash_algorithm

protected def to_string : hash_algorithm → string
| sha1 := "sha1"
| sha2_256 := "sha2_256"
| ripemd160 := "ripemd160"
| sha2_224 := "sha2_224"
| sha2_384 := "sha2_384"
| sha2_512 := "sha2_512"
| sha3_224 := "sha3_224"
| sha3_256 := "sha3_256"
| sha3_384 := "sha3_384"
| sha3_512 := "sha3_512"
| sm3      := "sm3"

instance : has_to_string hash_algorithm := ⟨ hash_algorithm.to_string ⟩

/- hash length in bytes -/
definition hash_length : hash_algorithm → ℕ
  | sha1      := 20
  | sha2_256  := 32
  | ripemd160 := 20
  | sha2_224  := 28
  | sha2_384  := 48
  | sha2_512  := 64
  | sha3_224  := 28
  | sha3_256  := 32
  | sha3_384  := 48
  | sha3_512  := 64
  | sm3       := 32

lemma max_hash_length (algo : hash_algorithm) : algo.hash_length ≤ 64 :=
begin
  cases algo,
  all_goals { dunfold hash_length },
  all_goals { galois.tactic.nat.nat_lit_le },
end

/- block length in bytes -/
definition block_length (algo : hash_algorithm) : ℕ :=
  match algo with
  | sha1      :=  64
  | sha2_256  :=  64
  | ripemd160 :=  64
  | sha2_224  :=  64
  | sha2_384  := 128
  | sha2_512  := 128
  | sha3_224  := 144
  | sha3_256  := 136
  | sha3_384  := 104
  | sha3_512  :=  72
  | sm3       :=  64
  end

definition encode (algo : hash_algorithm) : byte :=
  match algo with
  | sha1      := 0x0
  | sha2_256  := 0x1
  | ripemd160 := 0x2
  | sha2_224  := 0x3
  | sha2_384  := 0x4
  | sha2_512  := 0x5
  | sha3_224  := 0x7
  | sha3_256  := 0x8
  | sha3_384  := 0x9
  | sha3_512  := 0xA
  | sm3       := 0xB
  end

definition decode (w : byte) : option hash_algorithm :=
  if w = 0x0 then
    some sha1
  else if w = 0x1 then
    some sha2_256
  else if w = 0x2 then
    some ripemd160
  else if w = 0x3 then
    some sha2_224
  else if w = 0x4 then
    some sha2_384
  else if w = 0x5 then
    some sha2_512
  else if w = 0x7 then
    some sha3_224
  else if w = 0x8 then
    some sha3_256
  else if w = 0x9 then
    some sha3_384
  else if w = 0xA then
    some sha3_512
  else if w = 0xB then
    some sm3
  else
    none

@[simp]
lemma decode_encode (a : hash_algorithm) : decode (encode a) = some a :=
begin
  cases a,
  simp [encode, decode],
  all_goals {
    simp [encode, decode],
    smt_tactic.execute smt_tactic.solve_goals
  }
end

instance : decidable_eq hash_algorithm := by tactic.mk_dec_eq_instance

------------------------------------------------------------------------
-- hash

-- | Helper function to speed up length proofs below
def to_byte_list (m : ℕ) (v : bitvec (8 * m)) : list byte := cast rfl (@bitvec.split_vector 8 m v)

protected
lemma length_to_byte_list (m : ℕ) (v : bitvec (8 * m)) : (to_byte_list m v).length = m :=
vector.length_split_vector _ _

def nat_224_decompose : bitvec 224 → list byte := @to_byte_list 28
def nat_256_decompose : bitvec 256 → list byte := @to_byte_list 32
def nat_384_decompose : bitvec 384 → list byte := @to_byte_list 48
def nat_512_decompose : bitvec 512 → list byte := @to_byte_list 64

definition hash : hash_algorithm → list byte → list byte
| sha2_256  data := nat_256_decompose (crypto.sha256 data)
| sha2_224  data := nat_224_decompose (crypto.sha224 data)
| sha2_384  data := nat_384_decompose (crypto.sha384 data)
| sha2_512  data := nat_512_decompose (crypto.sha512 data)
| algo data := list.repeat 0 (algo.hash_length)

theorem length_hash_is_hash_length
: ∀ (algo : hash_algorithm) (data : list byte),
    (algo.hash data).length = algo.hash_length
| sha1      data := list.length_repeat _ _
| sha2_256  data := hash_algorithm.length_to_byte_list _ _
| ripemd160 data := list.length_repeat _ _
| sha2_224  data := hash_algorithm.length_to_byte_list _ _
| sha2_384  data := hash_algorithm.length_to_byte_list _ _
| sha2_512  data := hash_algorithm.length_to_byte_list _ _
| sha3_224  data := list.length_repeat _ _
| sha3_256  data := list.length_repeat _ _
| sha3_384  data := list.length_repeat _ _
| sha3_512  data := list.length_repeat _ _
| sm3       data := list.length_repeat _ _

-- Hash the data using the given algorithm.
definition hashv (algo : hash_algorithm) (data : list byte) : vector byte algo.hash_length :=
  ⟨ hash algo data, length_hash_is_hash_length algo data ⟩

end hash_algorithm

end hmac


