import Mathlib.Logic.Equiv.Basic

/-! # Subtype Equiv Congruence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SubtypeEquivCongruence

/-! Equality of reference parameters and actual values transports
the output of an already constructed family of subtype equivalences. -/

theorem subtypeFamilyEquiv_congr {R T M : Type*} (P : R → T → Prop)
    (E : ∀ r, {t // P r t} ≃ M) {r s : R} (h : r = s)
    (a : {t // P r t}) (b : {t // P s t}) (hab : a.val = b.val) : E r a = E s b := by
  subst s
  exact congrArg (E r) (Subtype.ext hab)

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SubtypeEquivCongruence
