/- This file defines a monad transformer for state, called monad.state_t that is
   similiar to the Haskell MTL type by the same name.
 -/
import galois.category.monad.state.class

universe variables u v

namespace monad

/- The state transformer -/
structure state_t (s : Type u) (m : Type u → Type v) (α : Type u) :=
(run : s → m (α × s))

namespace state_t

section

parameter {S : Type u}
parameter {M : Type u → Type v}

/- Two state_t values are equivalent if their underlying function is. -/
def eq {α : Type u} (x y : monad.state_t S M α) (p : x.run = y.run) : x = y :=
begin
  cases x with xr,
  cases y with yr,
  apply congr_arg,
  exact p,
end

def pure [applicative M] (α : Type u) (x : α) : monad.state_t S M α := ⟨λs, pure (x, s)⟩

def map [functor M] {α β : Type u} (f : α → β) (m : state_t S M α) : state_t S M β := ⟨ λs, do
  (λ(p : α × S), (f p.fst, p.snd)) <$> m.run s ⟩

def bind [monad M] {α β : Type u} (m : state_t S M α) (h : α → state_t S M β) : state_t S M β :=
⟨ λs, m.run s >>= λp, (h (p.fst))^.run (p.snd) ⟩

end

-- Map a computation over M into a computation over state_t.
def lift {S : Type u} {M : Type u → Type v} [functor M] {α : Type u} (m : M α) : state_t S M α :=
  { run := λs, (λv, (v, s)) <$> m }

/- Show state_t is a functor if the underlying action is a functor -/
instance is_functor (S : Type u) (M : Type u → Type v) [inst : functor M]
: functor (state_t S M) :=
{ map := @map S M inst
, id_map :=
  begin
    intros α x,
    cases x with f,
    apply eq,
    unfold map,
    dsimp,
    apply funext,
    intros s,
    transitivity,
    { change (λ (p : α × S), (id (p.fst), p.snd)) <$> f s = id <$> f s,
      apply congr_fun,
      apply congr_arg,
      apply funext,
      intro p,
      cases p,
      refl,
    },
    exact functor.id_map _,
  end
, map_comp :=
  begin
    intros α β γ f g m,
    dsimp [map],
    apply congr_arg,
    apply funext,
    intro s,
    rw [eq.symm (functor.map_comp _ _ (m.run s))],
  end
}

end state_t
end monad

/- Show state_t is a monad if the underlying action is a monad -/
instance monad.state_t.is_monad (S : Type u) (M : Type u → Type v) [inst : monad M]
  : monad (monad.state_t S M) :=
{ to_functor := @monad.state_t.is_functor S M inst.to_functor
, bind   := @monad.state_t.bind S M inst
, pure   := @monad.state_t.pure S M (by apply_instance)
, pure_bind :=
  begin
    intros α β x f,
    apply monad.state_t.eq,
    unfold has_bind.bind monad.state_t.bind has_pure.pure monad.state_t.pure,
    transitivity,
    apply funext,
    intro s,
    apply monad.pure_bind,
    simp,
  end
, bind_assoc :=
  begin
    intros α β γ m f g,
    apply monad.state_t.eq,
    unfold has_bind.bind monad.state_t.bind,
    apply funext,
    intro s,
    dsimp,
    apply monad.bind_assoc,
  end
, bind_pure_comp_eq_map :=
  begin
    unfold auto_param,
    intros α β f m,
    apply monad.state_t.eq,
    apply funext,
    intro s,
    simp [monad.state_t.bind, function.comp, monad.state_t.pure],
    transitivity,
    { change (m.run s >>= λ (p : α × S), pure (f (p.fst), p.snd))
           = (m.run s >>= pure ∘ λ p, (f p.fst, p.snd)),
      apply congr_arg,
      apply funext,
      intro p,
      refl,
    },
    transitivity,
    { apply monad.bind_pure_comp_eq_map, },
    unfold has_map.map monad.state_t.map,
  end
}

-- A typeclas for monad states.
-- Used to provide monad transformers.
@[reducible]
instance monad.state_t.is_monad_state (s : Type u) (m : Type u → Type v) [inst : monad m]
: monad.monad_state (monad.state_t s m) :=
{ to_monad := monad.state_t.is_monad s m
, state := s
, with_state := λα f, ⟨pure ∘ f⟩
}
