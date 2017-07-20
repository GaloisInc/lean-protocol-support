/- This defines a simple type for bytes. -/
import data.bitvec

-- A byte is a 8-bit bitvecotr
definition byte := bitvec 8

namespace bitvec
private def to_string {n : nat} : bitvec n → string
| ⟨bs, p⟩ :=
  "0b" ++ (bs.reverse.map (λ b : bool, if b then '1' else '0')).as_string

instance (n : nat) : has_to_string (bitvec n) :=
⟨to_string⟩
end bitvec

instance : has_zero byte := begin unfold byte, apply_instance end
instance : has_one byte  := begin unfold byte, apply_instance end
instance : has_add byte  := begin unfold byte, apply_instance end
instance : decidable_eq byte  := begin unfold byte, apply_instance end
instance : has_to_string byte := begin unfold byte, apply_instance end

definition word16 := bitvec 16

definition word32 := bitvec 32

definition word64 := bitvec 64

instance : has_zero word64 := begin unfold word64, apply_instance end
instance : has_one word64  := begin unfold word64, apply_instance end
instance : has_add word64  := begin unfold word64, apply_instance end
instance : decidable_eq word64  := begin unfold word64, apply_instance end
instance : has_to_string word64 := begin unfold word64, apply_instance end

def byte_to_word32 (w : byte) : word32 := @bitvec.append 24 8 0 w
def byte_to_word64 (w : byte) : word64 := @bitvec.append 56 8 0 w
def word16_to_byte (w : word16) : byte := vector.drop 8 w
