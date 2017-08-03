import .option

open tactic lean lean.parser
open interactive interactive.types expr

local postfix *:9001 := many

namespace tactic.interactive

private
meta def specialize_get_name : expr → tactic name
| (app f _) := specialize_get_name f
| (local_const _ n _ _) := pure n
| _ := fail "Not an application of a local constant"

meta def specialize (H : parse texpr) : tactic unit :=
  do result ← i_to_expr H,
     id ← specialize_get_name result,
     n ← get_unused_name id none,
     note n none result,
     to_remove ← get_local id, 
     tactic.clear to_remove,
     tactic.rename n id

universes u v

def congr_arg_f_equal {A : Sort u} {B : Sort v} {f f' : A → B}
  {x x' : A} : f = f' → x = x' → f x = f' x'
:= begin
intros H, induction H, intros H, induction H, reflexivity
end

meta def f_equal : tactic unit := do
  try (apply ``(@congr_arg_f_equal)),
  tactic.focus [ reflexivity <|> f_equal, try reflexivity ]

end tactic.interactive