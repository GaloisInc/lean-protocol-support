lemma nat.lt_succ_le : forall a b,
a < nat.succ b ->
a ≤ b :=
begin
intros,
cases a_1,
{
    refl,
},
{
    apply nat.le_trans,
    apply nat.le_add_right,
    exact 1,
    apply a_2
}
end

lemma nat.lt_succ_ne_lt : forall a b,
a < nat.succ b ->
a ≠ b ->
a < b :=
begin
intros,
cases  (nat.lt_trichotomy a b),
{  assumption },
{ cases a_3,
    { contradiction},
    {   exfalso,
        apply nat.le_lt_antisymm,
        apply a_1,
        apply nat.succ_lt_succ,
        assumption,
    }
}
end