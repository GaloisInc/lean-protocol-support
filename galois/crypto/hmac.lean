/- This defines an hmac primitive.
 -/
import galois.word

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
