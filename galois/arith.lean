import data.int.basic
import data.rat
import galois.nat.div_lemmas
import data.nat.basic
import galois.sum
import init.data.ordering

import galois.nat
import .bool

universe u

@[simp]
theorem coe_bool_to_prop (b:bool) : coe b ↔ b = tt :=
begin
  cases b; exact dec_trivial,
end
@[simp]
theorem to_bool_is_tt  (p : Prop) [inst:decidable p] : (to_bool p = tt) = p :=
begin
  cases inst,
  all_goals { unfold decidable.to_bool, simp [a], },
end

/-
namespace nat

lemma lt.intro {n m k : ℕ} (h : n + succ k = m) : n < m :=
  h ▸ nat.succ_le_succ (nat.le_add_right n k)

end nat

namespace list

section
parameter {α : Type u}
parameter (n : ℕ)
parameter (f : fin n → α)

protected
def generate_core : Π (i j : ℕ), i + j = n  → list α
| i 0 pr := []
| i (nat.succ j) pr :=
  let qr : i < n := nat.lt.intro pr in
  let rr : i+1 + j = n :=
      begin
        simp [nat.succ_add i j],
        exact pr,
      end in
  f ⟨i, qr⟩ :: generate_core (i+1) j rr

protected
def generate : list α := generate_core 0 n (nat.zero_add n)

theorem length_generate_core (i j : ℕ)
: Π (pr : i + j = n),
  (generate_core i j pr).length = j :=
begin
  revert i,
  induction j,
  case nat.zero {
    intros,
    exact dec_trivial,
  },
  case nat.succ j ind {
    intros,
    simp only [list.generate_core, length_cons],
    apply congr_arg nat.succ,
    apply ind,
  },
end

protected
theorem length_generate : generate.length = n :=
begin
  apply length_generate_core,
end

end

section foldl₂
parameter {α : Type _}
parameter {β : Type _}
parameter {C : Type _}
parameter (f : C → α → β → C)

def foldl₂
  : C → list α → list β → C
| c [] _ := c
| c _ [] := c
| c (x::xr) (y::yr) := foldl₂ (f c x y) xr yr

end foldl₂

section init
parameter {α : Type _}

protected
theorem length_init (l : list α) : l.init.length = l.length - 1 :=
begin
  induction l,
  case nil {
    simp [init],
  },
  case cons h r ind {
    cases r,
    { simp [init], },
    case list.cons h2 r {
      simp only [init, length_cons, ind, nat.succ_sub_succ],
      trivial,
    }
  }
end


end init
end list


namespace vector

def generate {α : Type u} (n : ℕ) (f : fin n → α) : vector α n :=
  ⟨ list.generate n f, list.length_generate n f⟩

section foldl₂
parameter {α : Type _}
parameter {β : Type _}
parameter {C : Type _}
parameter (f : C → α → β → C)
parameter {n:ℕ}

def foldl₂ (c:C) (x : vector α n) (y: vector β n) : C :=
  list.foldl₂ f c x.to_list y.to_list

end foldl₂

def dotprod {α: Type u} [semiring α] {n:ℕ} : vector α n → vector α n → α :=
  foldl₂ (λc a b, c + a * b) 0

notation `⬝` := dotprod

def last {α:Type u} {n:ℕ} (v : vector α (n+1)) : α :=
  v.to_list.last (list.ne_nil_of_length_eq_succ v.property)

-- Return all but the last element in a vector.
def init {α:Type u} {n:ℕ} (v : vector α (n+1)) : vector α n :=
  let pr : v.to_list.init.length = n :=
      begin
        simp only [list.length_init, to_list_length],
        trivial,
      end in
  ⟨ v.to_list.init, pr⟩

def scale_mul {α:Type u} [has_mul α] {n:ℕ} (c:α) (v : vector α n)
: vector α n :=
  v.map (has_mul.mul c)

end vector
-/


namespace list

protected
def maximum {α:Type _} [decidable_linear_order α] : list α → option α
| [] := option.none
| (h::r) := option.some (r.foldl max h)

protected
def minimum {α:Type _} [decidable_linear_order α] : list α → option α
| [] := option.none
| (h::r) := option.some (r.foldl min h)

end list

namespace rat

def to_string (q:ℚ) : string :=
  if q.denom = 1 then
    to_string (q.num)
  else
    to_string (q.num) ++ "/" ++ to_string q.denom

instance : has_to_string ℚ := ⟨ to_string ⟩

end rat

-----------------------------------------------------------------------
-- bound

-- Return true if either option is none, or both are defined and first is
-- less than second.
def bound_le : option ℚ → option ℚ → Prop
| none _ := true
| (some l) (some u) := l ≤ u
| (some _) none := true

theorem bound_le_maximum_minimum (ll ul : list ℚ)
(pr : ∀ (l u : ℚ), l ∈ ll → u ∈ ul → l ≤ u)
: bound_le (list.maximum ll) (list.minimum ul) := sorry

def le_bound (ol: option ℚ) (u : ℚ) : Prop :=
  match ol with
  | option.none := true
  | (option.some l) := l ≤ u
  end

instance le_bound.decidable (ol : option ℚ) (u:ℚ) : decidable (le_bound ol u) :=
  begin cases ol; unfold le_bound; apply_instance end

def ge_bound (l:ℚ) (ou: option ℚ) : Prop :=
  match ou with
  | option.none := true
  | (option.some u) := l ≤ u
  end

instance ge_bound.decidable (l:ℚ) (ou : option ℚ) : decidable (ge_bound l ou) :=
  begin cases ou; unfold ge_bound; apply_instance end


def choose_bound : option ℚ → option ℚ → ℚ
| (some l) _ := l
| none none := 0
| none (some u) := u

theorem le_bound_choose_bound (l u : option ℚ) : le_bound l (choose_bound l u) :=
begin
  cases l with l,
  all_goals { simp [le_bound, choose_bound], },
end

theorem ge_bound_choose_bound {l u : option ℚ} (pr : bound_le l u) : ge_bound (choose_bound l u) u :=
begin
  cases u with u,
  {
    simp [ge_bound, choose_bound],
  },
  {
    cases l with l,
    { simp [ge_bound, choose_bound], },
    { simp [bound_le] at pr,
      simp [ge_bound, choose_bound, pr],
    },
  },
end

-----------------------------------------------------------------------
-- assignment

@[reducible]
def assignment (α:Type _) (n:ℕ) := vector α n

namespace assignment

section
parameter {α:Type _}

/-- The empty assignment. -/
def empty : assignment α 0 := vector.nil

def zero_assignment_is_empty (a:assignment α 0) : a = empty :=
begin
  simp [empty],
  apply vector.eq_nil,
end

def concat {n:ℕ} (xs : assignment α n) (x : α) : assignment α (n+1) :=
  vector.cons x xs

def shrink {n:ℕ} (a:assignment α n) (i : fin n) : assignment α i.val :=
begin
have H1 : i.val ≤ n,
apply le_of_lt, apply fin.is_lt,
have H := vector.take i.val a,
unfold min at H,
rw (if_pos H1) at H, apply H
end

-- def last_of_fin {n:ℕ} (a:assignment α n) (i : fin n) : α :=
--   sorry

-- def init {n:ℕ} (a:assignment α (n+1)) : assignment α n :=
--   sorry

-- def last {n:ℕ} (a:assignment α (n+1)) : α :=
--   sorry

-- @[simp]
-- theorem init_concat {n:ℕ} (a:assignment α n) (z:α) : init (concat a z) = a := sorry

-- @[simp]
-- theorem last_concat {n:ℕ} (a:assignment α n) (z:α) : last (concat a z) = z := sorry

end
end assignment

-- denotes the inequality coef <= bound
inductive linear_expr : ℕ → Type
| const : Π {n:ℕ}, ℚ → linear_expr n
| add : Π {n:ℕ} (c:ℚ) (pr : c ≠ 0) (i : fin n), linear_expr i.val → linear_expr n

lemma nat_ordering_char (x y : ℕ)
  : (match nat.cmp x y with
  | ordering.lt := x < y
  | ordering.eq := x = y
  | ordering.gt := x > y
  end : Prop)
:= begin
dsimp [nat.cmp],
apply (if H : x < y then _ else _),
rw (if_pos H), assumption,
rw (if_neg H),
apply (if H' : x = y then _ else _),
rw (if_pos H'), assumption,
rw (if_neg H'), dsimp,
dsimp [(>)],
rw lt_iff_not_ge,
intros contra, apply H', apply le_antisymm,
assumption, apply le_of_not_gt, assumption,
end

namespace fin

lemma lt_char {n : ℕ}
  (x y : fin n) : x < y ↔ x.val < y.val
:= begin
induction x; induction y; reflexivity
end

def extend_le {m n : ℕ} (H : m ≤ n) (x : fin m) : fin n
:= begin
constructor, apply lt_of_lt_of_le, apply fin.is_lt, assumption,
assumption,
end

def restrict_lt {n : ℕ} (x y : fin n) (H : x < y)
  : fin y.val
:= ⟨ x.val, begin
rw lt_char at H, assumption
end ⟩

def ordering_elim {n : ℕ}
  (C : Sort _)
  (x y : fin n)
  (Hlt : x < y → C)
  (Heq : x = y → C)
  (Hgt : x > y → C)
  : C
:= begin
have H := nat_ordering_char x.val y.val,
cases (nat.cmp x.val y.val);
  dsimp at H,
{ apply Hlt, rw lt_char, assumption },
{ induction x, induction y, dsimp at H,
  apply Heq, subst H, },
{ apply Hgt, unfold gt, rw fin.lt_char, assumption },
end

end fin

namespace linear_expr

def scale_mul (x : ℚ) (xne0 : x ≠ 0) : ∀ {n}, linear_expr n → linear_expr n
| _ (const c) := const (x * c)
| _ (add c cne0 i e) := add (x * c) (mul_ne_zero xne0 cne0) i (scale_mul e)

def add_constant (x : ℚ) : ∀ {n}, linear_expr n → linear_expr n
| _ (const c) := const (x + c)
| _ (add c cne0 i e) := add c cne0 i (add_constant e)

def extend {i n :ℕ} : linear_expr i → i ≤ n → linear_expr n
| (const c) is_le := const c
| (add c pr j e) is_le := add c pr ⟨j.val, lt_of_lt_of_le j.is_lt is_le⟩ e

def add_variable (x : ℚ) : ∀ {n}, fin n → linear_expr n → linear_expr n
| _ i (const c) := if xne0 : x ≠ 0
    then add x xne0 i (const c)
    else const c
| n i (add c cne0 i' e) := begin
  apply (fin.ordering_elim (linear_expr n) i i');
    intros,
    { apply (add c cne0 i'),
      apply add_variable,
      apply fin.restrict_lt, assumption,
      assumption,
    },
    { apply (if H : x + c ≠ 0 then _ else _),
      { apply (add (x + c) H i' e), },
      { apply e.extend, apply le_of_lt, apply fin.is_lt, }
    },
    { apply (if H : x ≠ 0 then _ else _),
      { apply (add x H i),
        apply (add c cne0), admit, admit },
      { apply e.extend, apply le_of_lt, apply fin.is_lt, }
    }
   end

def sum : ∀ {n}, linear_expr n → linear_expr n → linear_expr n
| _ (const c) e := add_constant c e
| _ (add c cne0 i e) e' := sorry

def as_const : linear_expr 0 → ℚ
| (const c) := c
| (add _ _ i _) :=
  begin
    have is_lit := i.is_lt,
    have h := nat.not_lt_zero i.val,
    contradiction,
  end

def prepend_sum : string → string → string
| s "" := s
| s t := s ++ " + " ++ t


def to_string_core  : Π {n:ℕ}, linear_expr n → string → string
| _ (const c) s :=
   if s = "" then
     to_string c
  else if c = 0 ∧ s ≠ "" then
    s
  else
    s ++ " + " ++ to_string c
| _  (add c _ i e) s :=
  to_string_core e
    (if c = 1 then
       prepend_sum ("v" ++ to_string i) s
     else
       prepend_sum (to_string c ++"×v" ++ to_string i) s)

def to_string  {n:ℕ} (e:linear_expr n) : string := to_string_core e ""

def var {n:ℕ} (i : fin n) : linear_expr n := add 1 dec_trivial i (const 0)

/-- Return the last coefficient of the linear_expression. -/
def last {n:ℕ} : linear_expr (n+1) → ℚ
| (const c) := 0
| (add c pr i e) := if i.val = n then c else 0

/-- Return the expression with the last variable removed and the coefficient. -/
def drop_last {n:ℕ} : linear_expr (n+1) → linear_expr n
| (const c) := const c
| (add c pr i e) :=
  if i_lt_n : i.val < n then
    add c pr ⟨i.val, i_lt_n⟩ e
  else
    e.extend (nat.pred_le_pred i.is_lt)

section evaluate
parameter {n:ℕ}

def evaluate_core : ℚ → Π{n:ℕ}, linear_expr n → assignment ℚ n → ℚ
| r _ (const c) _ := c + r
| r _ (add c pr i e) a := evaluate_core (r + c * a.nth i) e (a.shrink i)

def evaluate : Π{n:ℕ}, linear_expr n → assignment ℚ n → ℚ := @evaluate_core 0

end evaluate

end linear_expr

-----------------------------------------------------------------------
-- linear_expr_list

def linear_expr_list (n:ℕ) := list (linear_expr n)

namespace linear_expr_list

def to_list {n:ℕ} : linear_expr_list n → list (linear_expr n) := id

instance (n:ℕ) : has_mem (linear_expr n) (linear_expr_list n) :=
  begin unfold linear_expr_list, apply_instance end

section
parameter {n:ℕ}

def evaluate (l : linear_expr_list n) (a : assignment ℚ n) : list ℚ :=
  l.map (λe, e.evaluate a)

theorem evaluate_cons (e : linear_expr n) (l : linear_expr_list n)
  (a : assignment ℚ n)
: evaluate (e :: l) a = e.evaluate a :: l.evaluate a := rfl

theorem mem_evaluate_implies {l: linear_expr_list n} {a:assignment ℚ n} {q : ℚ}
(pr : q ∈ l.evaluate a)
: ∃(e:linear_expr n), e ∈ l ∧ e.evaluate a = q
:= begin
apply list.exists_of_mem_map pr,
end

end
end linear_expr_list

---------------------------------------------------------
-- Inequalities

-- denotes the inequality lhs <= 0
structure inequality (n:ℕ) :=
(lhs : linear_expr n)

namespace inequality

section entails

parameter {n:ℕ}

def from_pair : linear_expr n → linear_expr n → inequality n := sorry

def satisfies (θ:assignment ℚ n) (c:inequality n) : Prop := c.lhs.evaluate θ ≤ 0

theorem satisfies_from_pair (a:assignment ℚ n) (l u:linear_expr n)
: satisfies a (from_pair l u) ↔ l.evaluate a ≤ u.evaluate a := sorry

instance (c:inequality n) (θ:assignment ℚ n)
: decidable (satisfies θ c) :=
  begin unfold satisfies, apply_instance end

end entails

notation `⊧` := satisfies

end inequality

/-- A collection on inequalities -/
def ineqs (n:ℕ) := list (inequality n)

namespace ineqs

instance (n:ℕ) : has_append (ineqs n) := begin unfold ineqs, apply_instance end
instance (n:ℕ) : has_mem (inequality n) (ineqs n) := begin unfold ineqs, apply_instance end

section satisfies

parameter {n:ℕ}
parameter (a:assignment ℚ n)

-- Returns true if assignment satisfies bound.
def satisfies (eqs:ineqs n) : Prop :=
   eqs.all (λb, to_bool (inequality.satisfies a b))

instance (eqs:ineqs n) : decidable (satisfies eqs) :=
  begin unfold satisfies, apply_instance end

@[simp]
theorem satisfies_nil : satisfies [] :=
begin
  simp [satisfies, list.all],
end

@[simp]
theorem satisfies_cons (h : inequality n) (r : ineqs n)
: satisfies (h :: r) ↔ inequality.satisfies a h ∧ satisfies r :=
begin
  simp [satisfies, list.all, list.foldr],
end

@[simp]
theorem satisfies_append (x y : ineqs n) :
 satisfies (x ++ y) = (satisfies x ∧ satisfies y) := sorry

end satisfies

theorem satisfies_list_implies_mem_satisfies {n:ℕ}
{e : inequality n}
{l : ineqs n}
{a:assignment ℚ n}
(pr : satisfies a l)
(in_list : e ∈ l)
: inequality.satisfies a e := sorry


/-- Denotes a solution to the equations. -/
def solution {n:ℕ} (eqs:ineqs n) := { a : assignment ℚ n // eqs.satisfies a }

/-- A proof that the equations are unsatisfiable. -/
def unsat_proof {n:ℕ} (eqs:ineqs n) :=
  ∀(a:assignment ℚ n), ¬ (satisfies a eqs)

end ineqs

-----------------------------------------------------------------------
-- bound

inductive bound (n:ℕ) : Type
-- lower e denotes e <= x
| lower : linear_expr n → bound
-- upper e denotes x <= e
| upper : linear_expr n → bound
-- If variable had a zero in the expression.
| independent  : inequality n → bound

namespace bound

/-- Given an inequality infers the resulting bound on the last variable. -/
def from_ineq {n:ℕ} (le : inequality (n+1)) : bound n :=
  let e := le.lhs in
  let c := e.last in
  let r  := e.drop_last in
   if c > 0 then
    -- "l + c * v <= 0" ~> "v <= -l/c"
    let recip := 1/c in
    bound.upper (linear_expr.scale_mul (-1/c) r)
    -- "l + c * v <= 0" ~> "l/c <= v"
  else if c < 0 then
    bound.lower (linear_expr.scale_mul (1/c) r)
  else
    bound.independent ⟨ r ⟩

section

parameter {n:ℕ}

-- Returns true if assignment satisfies bound.
def satisfies (a:assignment ℚ (n+1)) : bound n → Prop
| (lower e) := e.evaluate a.init ≤ a.last
| (upper e) := a.last ≤ e.evaluate a.init
| (independent le) := le.satisfies a.init

@[simp]
theorem satisfies_from_ineq (a: assignment ℚ (n+1)) (le : inequality (n+1))
: bound.satisfies a (bound.from_ineq le) = inequality.satisfies a le := sorry

end
end bound

-----------------------------------------------------------------------
-- bound_list

structure bound_list (n:ℕ) :=
(lower : linear_expr_list n)
(upper : linear_expr_list n)
(independent : ineqs n)

namespace bound_list

def empty (n:ℕ) : bound_list n :=
  { lower := [], upper := [], independent := []}

def lower_bound {n:ℕ} (b:bound_list n) (a:assignment ℚ n) : option ℚ :=
  (b.lower.evaluate a).maximum

def upper_bound {n:ℕ} (b:bound_list n) (a:assignment ℚ n) : option ℚ :=
  (b.upper.evaluate a).minimum

section satisfies
parameter {n:ℕ}
parameter (a:assignment ℚ (n+1))

-- Returns true if assignment satisfies bound.
def satisfies (b:bound_list n) : Prop :=
     le_bound (b.lower_bound a.init) a.last
   ∧ ge_bound a.last (b.upper_bound a.init)
   ∧ ineqs.satisfies a.init b.independent

instance (b:bound_list n) : decidable (satisfies b) :=
  begin
    unfold satisfies,
    apply_instance,
  end

end satisfies

@[simp]
theorem satisfies_empty (n:ℕ) (a:assignment ℚ (n+1))
: satisfies a (empty n) :=
begin
  simp [empty, satisfies, upper_bound, lower_bound,
        linear_expr_list.evaluate, list.minimum,
        ge_bound, le_bound],
end

section from_ineqs
parameter {n:ℕ}

def add_bound : bound n → bound_list n → bound_list n
| (bound.lower e) b := { b with lower := e :: b.lower }
| (bound.upper e) b := { b with upper := e :: b.upper }
| (bound.independent e) b := { b with independent := e :: b.independent }

theorem satisfies_add_bound (a:assignment ℚ (n+1)) (b:bound n) (l: bound_list n)
: satisfies a (bound_list.add_bound b l) ↔
  (bound.satisfies a b ∧ satisfies a l) :=
begin
  apply iff.intro,
  { cases b,
    case bound.lower e {
      cases l,
      simp [satisfies, add_bound, bound.satisfies, lower_bound, upper_bound],
      intros ineq_sat,
      constructor,
      { cc, },
      constructor,
      { admit,
      },
      constructor,
      { cc,
      },
      { admit,
      },
    },
    case bound.upper e {
      admit,
    },
    case bound.independent ineq {
      admit,
    },
  },
  {
    admit,
  }
end


/-- Return bounds on last variable. -/
def from_ineqs (l:ineqs (n+1)) : bound_list n :=
  l.foldr (λe, add_bound (bound.from_ineq e)) (empty n)

@[simp]
theorem from_ineqs_nil : from_ineqs list.nil = empty n := rfl

@[simp]
theorem from_ineqs_cons (e: inequality (n+1)) (l:ineqs (n+1))
: from_ineqs (e::l) =
   add_bound (bound.from_ineq e) (from_ineqs l) :=
begin
  simp [from_ineqs],
end

end from_ineqs

section
parameter {n:ℕ}

def to_ineqs (b:bound_list n) : ineqs n :=
  b.independent ++ (do l ← b.lower.to_list, inequality.from_pair l <$> b.upper.to_list)

theorem lower_upper_in_to_ineqs {l u:linear_expr n} {b: bound_list n}
(in_lower : l ∈ b.lower)
(in_upper : u ∈ b.upper)
: (inequality.from_pair l u ∈ to_ineqs b) := sorry

end

def solution {n:ℕ} (eqs:bound_list n) := { a : assignment ℚ (n+1) // eqs.satisfies a }


theorem to_ineqs_preserve_sat {n:ℕ} {b: bound_list n} (a:assignment ℚ (n+1))
(pr : bound_list.satisfies a b)
: ineqs.satisfies a.init b.to_ineqs :=
begin
  admit,
end

theorem lower_le_upper {n:ℕ} {b: bound_list n} (a:assignment ℚ n)
(pr : ineqs.satisfies a b.to_ineqs)
: bound_le (b.lower_bound a) (b.upper_bound a) :=
begin
  simp [lower_bound, upper_bound],
  apply bound_le_maximum_minimum,
  intros l u l_mem u_mem,
  apply exists.elim (linear_expr_list.mem_evaluate_implies l_mem),
  intros l_eq l_cond,
  apply exists.elim (linear_expr_list.mem_evaluate_implies u_mem),
  intros u_eq u_cond,
  have in_list := lower_upper_in_to_ineqs l_cond.left u_cond.left,
  have is_sat := ineqs.satisfies_list_implies_mem_satisfies pr in_list,
  simp [inequality.satisfies_from_pair] at is_sat,
  cc,
end

end bound_list

-----------------------------------------------------------------------
-- to_ineqs theorems



theorem bounded_list.satisfies_concat {n:ℕ} {b: bound_list n} (a:assignment ℚ n) {z : ℚ}
(pr : ineqs.satisfies a b.to_ineqs)
(sat_lower : le_bound (b.lower_bound a) z)
(sat_upper : ge_bound z (b.upper_bound a))
: bound_list.satisfies (a.concat z) b :=
begin
  unfold bound_list.satisfies,
  simp,
  simp [bound_list.to_ineqs] at pr,
  cc,
end

-----------------------------------------------------------------------
-- from_ineqs theorems

theorem from_ineqs_preserve_sat {n:ℕ} {l: ineqs (n+1)} (a:assignment ℚ (n+1))
: bound_list.satisfies a (bound_list.from_ineqs l) ↔ ineqs.satisfies a l :=
begin
  induction l,
  case list.nil { simp, },
  case list.cons h r ind {
    simp [bound_list.satisfies_add_bound],
    cc,
  },
end

def ineqs.solution.to_bound_list {n:ℕ} {b : bound_list n}
  : b.to_ineqs.solution → b.solution
| ⟨ a, pr ⟩ :=
  let z : ℚ := choose_bound (b.lower_bound a) (b.upper_bound a) in
  let qr : b.satisfies (assignment.concat a z) :=
        begin
          apply bounded_list.satisfies_concat _ pr,
          {
            apply le_bound_choose_bound,
          },
          {
            apply ge_bound_choose_bound,
            apply bound_list.lower_le_upper,
            apply pr,
          }
        end in
  ⟨ (a.concat z : assignment ℚ (n+1)), qr ⟩

def bound_list.solution.to_ineqs {n:ℕ} {l : ineqs (n+1)}
  : (bound_list.from_ineqs l).solution → l.solution
  | ⟨ a, pr ⟩ :=
    let qr : l.satisfies a := iff.mp (from_ineqs_preserve_sat _) pr in
    ⟨ a, qr ⟩

inductive sat_result {n:ℕ} (eqs:ineqs n)
| unsat : eqs.unsat_proof → sat_result
| sat : eqs.solution → sat_result

def solve_inequalities : Π {n:ℕ} (eqs:ineqs n), sat_result eqs
| 0 l :=
  if pr : l.satisfies assignment.empty then
    sat_result.sat ⟨ assignment.empty, pr ⟩
  else
    sat_result.unsat
    (begin
      unfold ineqs.unsat_proof,
      intros a,
      rw [assignment.zero_assignment_is_empty a],
      exact pr,
    end)
| (nat.succ n) l :=
  match solve_inequalities (bound_list.from_ineqs l).to_ineqs with
  | sat_result.sat a := sat_result.sat a.to_bound_list.to_ineqs
  | sat_result.unsat pr := sat_result.unsat $
     begin
       unfold ineqs.unsat_proof,
       intros a contra,
       unfold ineqs.unsat_proof at pr,
       apply pr a.init,
       apply bound_list.to_ineqs_preserve_sat a,
       apply iff.mpr (from_ineqs_preserve_sat a),
       exact contra,
     end
  end


-----------------------------------------------------------------------
-----------------------------------------------------------------------
-- Meta

open tactic

namespace linear

inductive type : Type
| nat : type
| int : type
| rat : type

meta def type.resolve : expr → string ⊕ type
| `(nat) := pure type.nat
| `(int) := pure type.int
| `(rat) := pure type.rat
| e := sum.inl ("Unknown type:" ++ to_string e)

set_option pp.all true

meta inductive lexpr : type → Type
| foreign : Π(tp:type), expr → lexpr tp
| add : Π{tp:type}, lexpr tp → lexpr tp → lexpr tp
| zero : Π(tp:type), lexpr tp
| one : Π(tp:type), lexpr tp
| bit0 : Π{tp:type}, lexpr tp → lexpr tp
| bit1 : Π{tp:type}, lexpr tp → lexpr tp

protected
meta def lexpr.resolve : Π(tp:type), expr → lexpr tp
| ltp `(@has_add.add %%tp %%inst %%x %%y) := lexpr.add (lexpr.resolve ltp x) (lexpr.resolve ltp y)
| ltp `(@has_zero.zero %%tp %%inst) := lexpr.zero ltp
| ltp `(@has_one.one %%tp %%inst)   := lexpr.one ltp
| ltp `(@bit0 %%tp %%inst %%x)                := lexpr.bit0 (lexpr.resolve ltp x)
| ltp `(@bit1 %%tp %%one_inst %%add_inst %%x) := lexpr.bit1 (lexpr.resolve ltp x)
| ltp e := lexpr.foreign ltp e

namespace lexpr

section to_string

protected
meta def to_string : ∀ {tp:type}, lexpr tp → string
| tp (foreign ._ x) := "<" ++ has_to_string.to_string x ++ ">"
| _ (add x y) := "(add " ++ to_string x ++ " " ++ to_string y ++ ")"
| tp (zero ._) := "(zero)"
| tp (one ._) := "(one)"
| _ (bit0 x) := "(bit0 " ++ to_string x ++ ")"
| _ (bit1 x) := "(bit1 " ++ to_string x ++ ")"

meta instance {tp:type} : has_to_string (lexpr tp) := ⟨@lexpr.to_string tp⟩

end to_string


end lexpr

meta inductive prop : Type
| eq : Π(tp:type), lexpr tp → lexpr tp → prop
| ge : Π(tp:type), lexpr tp → lexpr tp → prop
| gt : Π(tp:type), lexpr tp → lexpr tp → prop
| le : Π(tp:type), lexpr tp → lexpr tp → prop
| lt : Π(tp:type), lexpr tp → lexpr tp → prop

set_option pp.all true

meta def prop.mk_bin (f : Π(tp:type), lexpr tp → lexpr tp → prop)
   (resolve_tp : string ⊕ type) (l r : expr) : string ⊕ prop := do
   tp ← resolve_tp,
   pure (f tp (lexpr.resolve tp l) (lexpr.resolve tp r))

/- Resovle an expression into a prop.

N.B. This may do the wrong thing if the expression contains a
non-standard typeclass instance for a primitive type.
-/
meta def prop.resolve : expr → string ⊕ prop
| `(@eq.{1}    %%tp        %%l %%r) :=
  prop.mk_bin prop.eq (type.resolve tp) l r
| `(@ge        %%tp %%inst %%l %%r) := prop.mk_bin prop.ge (type.resolve tp) l r
| `(@gt        %%tp %%inst %%l %%r) := prop.mk_bin prop.gt (type.resolve tp) l r
| `(@has_le.le %%tp %%inst %%l %%r) := prop.mk_bin prop.ge (type.resolve tp) l r
| `(@has_lt.lt %%tp %%inst %%l %%r) := prop.mk_bin prop.gt (type.resolve tp) l r
| _ := sum.inl "Unknown expr"

namespace prop

protected
meta def to_string : prop → string
| (eq tp l r) := "eq " ++ l.to_string ++ " " ++ r.to_string
| (ge tp l r) := "ge " ++ l.to_string ++ " " ++ r.to_string
| (gt tp l r) := "gt " ++ l.to_string ++ " " ++ r.to_string
| (le tp l r) := "le " ++ l.to_string ++ " " ++ r.to_string
| (lt tp l r) := "lt " ++ l.to_string ++ " " ++ r.to_string

meta instance : has_to_string prop := ⟨ prop.to_string ⟩

end prop


meta def linear_solve : tactic unit := do
  intros,
  ctx ← local_context,
  ctx_types ← ctx.mmap infer_type,
  let pp (e : expr) : tactic unit := (do
        match prop.resolve e with
        | sum.inl msg :=
           trace (msg ++ "\n" ++ to_string e)
        | (sum.inr p) := do
          trace (to_string p)
        end),
  _ ← ctx_types.mmap pp,
  t ← target,
  match t with
  | `(true) := do
    trace (to_string (ctx.length)),
    exact `(true.intro)
  | _ := do
    let i := ctx_types.index_of t,
    if i < ctx.length then do
      match ctx.nth i with
      | (option.some pr) := exact pr
      | option.none := fail "ctx.nth failed"
      end
    else trace "nope", pure ()
  end

example (x y : ℕ) : x = 0 → x = 1 → y = 2 → y = 3 → x = 1 :=
begin
  intro p,
--  cc,

  linear_solve,

end

end linear
