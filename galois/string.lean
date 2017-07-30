/-
Additional operations for strings.
-/

namespace string

def from_list : list char → string
| [] := string.empty
| (c::r) := c.to_string ++ from_list r

def repeat (s : string) : ℕ → string
| 0 := ""
| (nat.succ i) := repeat i ++ s

end string
