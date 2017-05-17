universe variables u v w

namespace list

variable {m : Type u → Type v}

@[simp]
theorem mfoldl_nil [monad m]
                   {s : Type u}
                   {α : Type w}
                   (f : s → α → m s)
                   (x : s)
: mfoldl f x nil = pure x :=
by simp [mfoldl, return]

theorem mfoldl_cons [monad m]
                    {s : Type u}
                    {α : Type w}
                    (f : s → α → m s)
                    (x : s)
                    (h : α)
                    (r : list α)
: mfoldl f x (h :: r) =  f x h >>= λy, mfoldl f y r :=
by simp [mfoldl]

end list
