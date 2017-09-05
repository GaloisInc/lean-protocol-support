import .temporal

universes u

namespace temporal
namespace classical

lemma not_always_not_implies_eventually {T : Type u} (P : tProp T)
  : ⊩ tNot (□ (tNot P)) => ◇ P
:= begin
intros tr notalways,
apply classical.by_contradiction,
intros contra, apply notalways,
intros n contra', apply contra,
constructor, assumption
end

end classical
end temporal