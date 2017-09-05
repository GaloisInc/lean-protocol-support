import order order.complete_lattice

open lattice

reserve infixl ` ⇒ `:60
reserve infixl ` ⊢ `:50
reserve infixl ` & `:70

infix ⇒ := has_imp.imp

universes u v

inductive rlist (A : Type u) : Type u
| nil {} : rlist
| snoc {} : rlist → A → rlist

infix & := rlist.snoc

namespace rlist

def map {A : Type u} {B : Type v} (f : A → B) : rlist A → rlist B
| nil := nil
| (xs & x) := map xs & f x

inductive mem {A : Type u} : A → rlist A → Prop
| here : ∀ x xs, mem x (xs & x)
| there : ∀ x y ys, mem x ys → mem x (ys & y)

instance has_mem (A : Type u) : has_mem A (rlist A)
:= ⟨ mem ⟩

instance mem_decidable (A : Type u) [decidable_eq A]
  (x : A) (xs : rlist A) : decidable (x ∈ xs)
:= begin
induction xs,
{ apply decidable.is_false, intros contra, cases contra, },
{ induction ih_1,
  { apply (if H : x = a_1 then _ else _),
    subst a_1, apply decidable.is_true, constructor,
    apply decidable.is_false, intros contra,
    cases contra, cc, apply a_2, assumption,
  },
  { apply decidable.is_true, constructor, assumption }
}
end

lemma map_mem {A : Type u} {B : Type v} (f : A → B) (x : A)
  (xs : rlist A)
  (H : x ∈ xs) : f x ∈ xs.map f
:= begin
induction H; dsimp [map], constructor, constructor, assumption,
end

end rlist

/-- complete heyting algebra -/
class cha (α : Type u) extends complete_lattice α, has_imp α : Type u :=
  (intro : ∀ {Γ P Q : α}, (Γ ⊓ P ≤ Q) → (Γ ≤ P ⇒ Q))
  (revert : ∀ {Γ P Q : α}, (Γ ≤ P ⇒ Q) → (Γ ⊓ P ≤ Q))

namespace cha
section cha_facts
parameters (α : Type u) [cha α]

def imp_adjunction {Γ P Q : α}
  : (Γ ⊓ P ≤ Q) = (Γ ≤ P ⇒ Q)
:= begin
apply propext, split, apply cha.intro, apply cha.revert,
end

end cha_facts
end cha

namespace sequent
section entails
parameters {α : Type u} [bounded_lattice α]

def conjunction  : rlist α → α
| rlist.nil := ⊤
| (Ps & P) := conjunction Ps ⊓ P

def entails (Γ : rlist α) (A : α)
  := conjunction Γ ≤ A
end entails

infix ⊢ := entails

section logic
parameters {α : Type u} [cha α]

def assumption {Γ : rlist α} {P : α} (H : P ∈ Γ)
  : Γ ⊢ P
:= begin
unfold entails,
induction H; dsimp [conjunction],
{ apply inf_le_right, },
{ apply le_trans, apply inf_le_left, assumption, }
end

def intro {Γ : rlist α} {P Q : α}
  (H : (Γ & P) ⊢ Q)
     : Γ ⊢ (P ⇒ Q)
:= begin
dsimp [entails, conjunction] at H,
apply cha.intro, assumption
end

def revert {Γ : rlist α} {P Q : α}
  (H : Γ ⊢ (P ⇒ Q))
  : (Γ & P) ⊢ Q
:= begin
dsimp [entails, conjunction],
apply cha.revert, assumption
end

def entails_top {Γ : rlist α}
  : Γ ⊢ ⊤
:= begin
dsimp [entails], apply le_top,
end

def split {Γ : rlist α} {P Q : α}
  (HP : Γ ⊢ P)
  (HQ : Γ ⊢ Q)
  : Γ ⊢ P ⊓ Q
:= begin
dsimp [entails] at *,
apply le_inf; assumption
end

def left {Γ : rlist α} {P Q : α}
  (HP : Γ ⊢ P)
  : Γ ⊢ P ⊔ Q
:= begin
dsimp [entails] at *,
apply le_trans, assumption, apply le_sup_left,
end

def right {Γ : rlist α} {P Q : α}
  (HP : Γ ⊢ Q)
  : Γ ⊢ P ⊔ Q
:= begin
dsimp [entails] at *,
apply le_trans, assumption, apply le_sup_right,
end

def apply_lemma_conj {Γ Δ : rlist α} {P : α}
   (H : Δ ⊢ P)
   (Hassumptions : Γ ⊢ conjunction Δ)
   : Γ ⊢ P
:= begin
apply le_trans; assumption,
end

def prove_conjunction_helper (Γ : rlist α)
  : rlist α → Prop
| rlist.nil := true
| (xs & x) := prove_conjunction_helper xs ∧ Γ ⊢ x

def prove_conjunction {Γ Δ : rlist α}
  (H : prove_conjunction_helper Γ Δ)
  : Γ ⊢ conjunction Δ
:= begin
induction Δ;
  dsimp [prove_conjunction_helper] at H;
  dsimp [conjunction],
apply entails_top, induction H with H1 H2,
apply split, apply ih_1, assumption, assumption,
end

def apply_lemma (Γ : rlist α) (P : α)
   {Δ : rlist α}
   (H : Δ ⊢ P)
   (Hassumptions : prove_conjunction_helper Γ Δ)
   : Γ ⊢ P
:= begin
apply apply_lemma_conj, assumption,
apply prove_conjunction, assumption,
end

def cut (Γ : rlist α) (Q : α) (P : α)
  (HP : Γ ⊢ P)
  (H : Γ & P ⊢ Q)
  : Γ ⊢ Q
:= begin
apply apply_lemma_conj H,
dsimp [conjunction], apply split,
apply le_refl, assumption
end



lemma test (P Q : α) : rlist.nil & P & Q ⊢ Q :=
begin
apply assumption, constructor,
end


end logic

end sequent