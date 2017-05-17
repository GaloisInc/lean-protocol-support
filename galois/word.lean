/- This defines a simple type for bytes. -/
import data.bitvec

-- A byte is a 8-bit bitvecotr
definition byte := bitvec 8

instance : has_zero byte := begin unfold byte, apply_instance end
instance : has_one byte  := begin unfold byte, apply_instance end
instance : has_add byte  := begin unfold byte, apply_instance end
instance : decidable_eq byte  := begin unfold byte, apply_instance end
instance : has_to_string byte := begin unfold byte, apply_instance end

definition word16 := bitvec 16

definition word32 := bitvec 32

definition word64 := bitvec 64

def byte_to_word32 (w : byte) : word32 := @bitvec.append 24 8 0 w
def byte_to_word64 (w : byte) : word64 := @bitvec.append 56 8 0 w
def word16_to_byte (w : word16) : byte := vector.dropn 8 w
