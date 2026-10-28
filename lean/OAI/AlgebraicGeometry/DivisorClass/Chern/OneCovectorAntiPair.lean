import OAI.AlgebraicGeometry.DivisorClass.Chern.OneCovectorAntiProjection
import OAI.AlgebraicGeometry.DivisorClass.Chern.AntiCovectorMetricDual

/-! # One Covector Anti Pair -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.OneCovectorAntiPair

noncomputable section

/-! Projection of an arbitrary test fiber does not change its real metric pairing with an antiholomorphic covector. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [Fintype ι] [LinearOrder ι]

omit [FiniteDimensional ℝ E] in
theorem oneCovectorAntiProjection_re (c : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) :
    Complex.reCLM.comp (AntiOneFormCoordinates.oneFormLinear (OneCovectorAntiProjection.oneCovectorAntiProjection c)) =
      (1 / 2 : ℝ) • (Complex.reCLM.comp (AntiOneFormCoordinates.oneFormLinear c) -
        (Complex.imCLM.comp (AntiOneFormCoordinates.oneFormLinear c)).comp (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)) := by
  ext v
  simp only [ContinuousLinearMap.comp_apply, AntiOneFormCoordinates.oneFormLinear_apply, OneCovectorAntiProjection.oneCovectorAntiProjection_apply,
    _root_.smul_apply, _root_.sub_apply, ContinuousLinearMap.lsmul_apply,
    Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul, Complex.mul_re, Complex.add_re,
    Complex.I_re, Complex.I_im, zero_mul, one_mul]
  norm_num
  ring

omit [FiniteDimensional ℝ E] in
theorem oneCovectorAntiProjection_im (c : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) :
    Complex.imCLM.comp (AntiOneFormCoordinates.oneFormLinear (OneCovectorAntiProjection.oneCovectorAntiProjection c)) =
      (1 / 2 : ℝ) • (Complex.imCLM.comp (AntiOneFormCoordinates.oneFormLinear c) +
        (Complex.reCLM.comp (AntiOneFormCoordinates.oneFormLinear c)).comp (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)) := by
  ext v
  simp only [ContinuousLinearMap.comp_apply, AntiOneFormCoordinates.oneFormLinear_apply, OneCovectorAntiProjection.oneCovectorAntiProjection_apply,
    _root_.smul_apply, _root_.add_apply, ContinuousLinearMap.lsmul_apply,
    Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul, Complex.mul_im, Complex.add_im,
    Complex.I_re, Complex.I_im, zero_mul, one_mul]
  norm_num

theorem bilinearFormMetricPair_anti_projection_re (b : Module.Basis ι ℝ E)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ v w, B v w = B w v)
    (hpos : ∀ v : E, v ≠ 0 → 0 < B v v)
    (hBJ : ∀ v w, B (Complex.I • v) w = -B v (Complex.I • w))
    (a c : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 0 1 a) :
    (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 B a (OneCovectorAntiProjection.oneCovectorAntiProjection c)).re =
      (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 B a c).re := by
  rw [OneCovectorMetricSharp.bilinearFormMetricPair_one_re_sharp b B hB hpos,
    OneCovectorMetricSharp.bilinearFormMetricPair_one_re_sharp b B hB hpos,
    oneCovectorAntiProjection_re, oneCovectorAntiProjection_im]
  simp only [map_smul, map_sub, map_add, Analysis.HodgeTheory.Decomposition.MetricDualBasis.Constructions.bilinearMetricSharp_comp_J B hpos hBJ,
    sub_neg_eq_add, map_neg, Complex.add_re, Complex.add_im, Complex.neg_im,
    Complex.smul_re, Complex.smul_im, smul_eq_mul,
    AntiCovectorMetricDual.antiOneCovector_re_J a ha, AntiCovectorMetricDual.antiOneCovector_im_J a ha]
  ring

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.OneCovectorAntiPair
