import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.VariableMetricIntegral

/-! # Pair Separation -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric

noncomputable section

/-! Uniqueness from the actual real metric pairing on original smooth bundle forms. -/

open _root_.TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : Data.HolomorphicLineMetricData u) (n : ℕ)

theorem Data.HolomorphicLineMetricData.formIntegralPair_sub_left (a b c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    h.formIntegralPair V n (a - b) c = h.formIntegralPair V n a c - h.formIntegralPair V n b c := by
  have hab : a - b = a + (-1 : ℂ) • b := by simp only [neg_smul, one_smul, sub_eq_add_neg]
  rw [hab, h.formIntegralPair_add_left, h.formIntegralPair_smul_left]
  simp only [map_neg, map_one, neg_one_mul, sub_eq_add_neg]

theorem Data.HolomorphicLineMetricData.formIntegralPair_real_separates_left
    (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)
    (hab : ∀ c, (h.formIntegralPair V n a c).re = (h.formIntegralPair V n b c).re) : a = b := by
  apply sub_eq_zero.mp
  apply h.formIntegralPair_definite V n (a - b)
  rw [h.formIntegralPair_sub_left, Complex.sub_re, hab (a - b), sub_self]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric
