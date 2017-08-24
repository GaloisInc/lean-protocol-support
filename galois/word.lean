/- This defines a simple type for bytes. -/
import init.data.string

-- A byte is a 8-bit bitvecotr
definition byte := bitvec 8

instance : has_zero byte := begin unfold byte, apply_instance end
instance : has_one byte  := begin unfold byte, apply_instance end
instance : has_add byte  := begin unfold byte, apply_instance end
instance : decidable_eq byte  := begin unfold byte, apply_instance end

protected
def byte.as_hex_digit (b:bitvec 4) : string :=
  if b = 0x0 then "0"
  else if b = 0x1 then "1"
  else if b = 0x2 then "2"
  else if b = 0x3 then "3"
  else if b = 0x4 then "4"
  else if b = 0x5 then "5"
  else if b = 0x6 then "6"
  else if b = 0x7 then "7"
  else if b = 0x8 then "8"
  else if b = 0x9 then "9"
  else if b = 0xA then "a"
  else if b = 0xB then "b"
  else if b = 0xC then "c"
  else if b = 0xD then "d"
  else if b = 0xE then "e"
  else "f"

-- Print a byte as a pair of hex digits
protected def byte.as_hex (b:byte) : string
  := byte.as_hex_digit (b.take 4)
  ++ byte.as_hex_digit (b.drop 4)

instance : has_to_string byte := ⟨ λb, "0x" ++ b.as_hex ⟩

-- Map a list of bytes to a string
protected
def byte.list_as_ascii (l : list byte) : string :=
  list.as_string $ list.map (λ(w:byte), char.of_nat w.to_nat) l

-- Map a list of bytes to a string
protected
def byte.list_from_ascii (s : string) : list byte :=
  list.map (λ(w:char), bitvec.of_nat 8 w.to_nat) s.to_list

-- Print the list of bytes as a series of hex digits.
def byte.list_as_hex : list byte → string := list.foldl (λs b, s ++ b.as_hex) ""

definition word16 := bitvec 16

instance : has_zero word16 := begin unfold word16, apply_instance end
instance : has_one word16  := begin unfold word16, apply_instance end
instance : has_add word16  := begin unfold word16, apply_instance end
instance : decidable_eq word16  := begin unfold word16, apply_instance end
instance : has_to_string word16 := ⟨ λx, to_string (x.to_nat) ⟩

definition word32 := bitvec 32

instance : has_zero word32 := begin unfold word32, apply_instance end
instance : has_one word32  := begin unfold word32, apply_instance end
instance : has_add word32  := begin unfold word32, apply_instance end
instance : decidable_eq word32  := begin unfold word32, apply_instance end
instance : has_to_string word32 := ⟨ λx, to_string (x.to_nat) ⟩

definition word64 := bitvec 64

instance : has_zero word64 := begin unfold word64, apply_instance end
instance : has_one word64  := begin unfold word64, apply_instance end
instance : has_add word64  := begin unfold word64, apply_instance end
instance : decidable_eq word64  := begin unfold word64, apply_instance end
instance : has_to_string word64 := ⟨ λx, to_string (x.to_nat) ⟩

def byte_to_word32 (w : byte) : word32 := @bitvec.append 24 8 0 w
def byte_to_word64 (w : byte) : word64 := @bitvec.append 56 8 0 w
def word16_to_byte (w : word16) : byte := vector.drop 8 w
