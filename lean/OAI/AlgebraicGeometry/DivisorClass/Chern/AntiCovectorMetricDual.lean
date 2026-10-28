import OAI.AlgebraicGeometry.DivisorClass.Chern.OneCovectorMetricSharp

/-! # Anti Covector Metric Dual -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.AntiCovectorMetricDual

noncomputable section

/-! The imaginary metric dual of an actual antiholomorphic covector is minus the complex rotation of its real metric dual. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

variable (B : E →L[ℝ] E →L[ℝ] ℝ)
  (hpos : ∀ v : E, v ≠ 0 → 0 < B v v)
  (hBJ : ∀ v w, B (Complex.I • v) w = -B v (Complex.I • w))
  (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 0 1 a)

include ha

omit [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] in
theorem antiOneCovector_re_J (w : E) :
    (AntiOneFormCoordinates.oneFormLinear a (Complex.I • w)).re = (AntiOneFormCoordinates.oneFormLinear a w).im := by
  rw [AntiOneFormCoordinates.oneFormLinear_complex_smul ha]
  simp [Complex.mul_re]

omit [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] in
theorem antiOneCovector_im_J (w : E) :
    (AntiOneFormCoordinates.oneFormLinear a (Complex.I • w)).im = -(AntiOneFormCoordinates.oneFormLinear a w).re := by
  rw [AntiOneFormCoordinates.oneFormLinear_complex_smul ha]
  simp [Complex.mul_im]

include hpos hBJ

theorem antiOneCovector_im_sharp :
    Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (Complex.imCLM.comp (AntiOneFormCoordinates.oneFormLinear a)) =
      -(Complex.I • Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (Complex.reCLM.comp (AntiOneFormCoordinates.oneFormLinear a))) := by
  have him : Complex.imCLM.comp (AntiOneFormCoordinates.oneFormLinear a) =
      (Complex.reCLM.comp (AntiOneFormCoordinates.oneFormLinear a)).comp (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) := by
    ext w
    exact (antiOneCovector_re_J a ha w).symm
  rw [him]
  exact Analysis.HodgeTheory.Decomposition.MetricDualBasis.Constructions.bilinearMetricSharp_comp_J B hpos hBJ _

theorem antiOneCovector_metric_norm {ι : Type} [Fintype ι] [LinearOrder ι]
    (b : Module.Basis ι ℝ E) (hB : ∀ v w, B v w = B w v) :
    let r := Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (Complex.reCLM.comp (AntiOneFormCoordinates.oneFormLinear a))
    (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 B a a).re = 2 * B r r := by
  rw [OneCovectorMetricSharp.bilinearFormMetricPair_one_re_sharp b B hB hpos,
    antiOneCovector_im_sharp B hpos hBJ a ha, map_neg, Complex.neg_im, antiOneCovector_im_J a ha,
    neg_neg]
  dsimp only
  rw [Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp_pair B hpos]
  change _ = 2 * (AntiOneFormCoordinates.oneFormLinear a (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (Complex.reCLM.comp (AntiOneFormCoordinates.oneFormLinear a)))).re
  ring

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.AntiCovectorMetricDual
