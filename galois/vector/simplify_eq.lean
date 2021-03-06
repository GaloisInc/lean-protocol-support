/- Defines basic lemmas for equality  -/
import data.vector
import ..list.simplify_eq
import ..list.take_drop_lemmas
import ..subtype

universe variables u

namespace vector

variable {α : Type u}
variable {n : ℕ}

local infix `++`:65 := vector.append


theorem cons_eq_cons {n : ℕ} (a b : α) (x y : vector α n)
: a :: x = b :: y ↔ a = b ∧ x = y :=
begin
  apply iff.intro,
  {
    -- Reduce to list primitives
    cases x with xv xp,
    cases y with yv yp,
    simp [ vector.cons ],
    -- Simplify equalities
    simp [ @subtype.mk_eq_mk (list α) (λ (l : list α), @list.length α l = nat.succ n)
         ],
    cc,
  },
  {
    intro h,
    rw [and.left h, and.right h],
  },
end

@[simp]
theorem append_eq_append {m n : ℕ} (a b : vector α m) (x y : vector α n)
: a ++ x = b ++ y ↔ a = b ∧ x = y :=
begin
  apply iff.intro,
  { -- Reduce intro list functions
    cases a with av ap,
    cases b with bv bp,
    cases x with xv xp,
    cases y with yv yp,
    unfold vector.append,

    have h : av^.length = bv^.length, { simp [ap, bp] },
    -- Simplify hypothesis into conjunction av = bv ∧ xv = yv
    intro p,
    have q := congr_arg subtype.val p,
    simp [list.append_eq_take_drop, h, nat.sub_self] at q,

    -- Prove equalities
    simp [and.left q, and.right q],
  },
  { -- Prove a = b & x = y -> a +++ x = b +++ y
    intro h,
    rw [and.left h, and.right h],
  },
end

end vector
