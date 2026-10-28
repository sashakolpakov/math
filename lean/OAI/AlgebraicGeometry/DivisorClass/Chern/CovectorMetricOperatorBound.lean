import OAI.AlgebraicGeometry.DivisorClass.Chern.CovectorMetricCutoffBound
import OAI.AlgebraicGeometry.DivisorClass.Chern.OneCovectorMetricBound

/-! # Covector Metric Operator Bound -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CovectorMetricOperatorBound

noncomputable section

/-! Operator norm estimates imply actual metric bounds between covector degrees. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

omit [FiniteDimensional ℝ E] in
theorem bilinearFormMetricPair_between_degrees_bound (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (c : Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    (U R M : ℝ) (hU : 0 ≤ U) (hR : 0 ≤ R)
    (hc : (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B c c).re ≤ U * ‖c‖ ^ 2)
    (hca : ‖c‖ ≤ R * ‖a‖)
    (ha : ‖a‖ ^ 2 ≤ M * (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 B a a).re) :
    (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B c c).re ≤
      (U * R ^ 2 * M) * (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 B a a).re := by
  have hs := (sq_le_sq₀ (norm_nonneg c) (mul_nonneg hR (norm_nonneg a))).mpr hca
  rw [mul_pow] at hs
  calc
    _ ≤ U * (R ^ 2 * ‖a‖ ^ 2) := hc.trans (mul_le_mul_of_nonneg_left hs hU)
    _ ≤ U * (R ^ 2 * (M * (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 B a a).re)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ha (sq_nonneg R)) hU
    _ = _ := by ring

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CovectorMetricOperatorBound
