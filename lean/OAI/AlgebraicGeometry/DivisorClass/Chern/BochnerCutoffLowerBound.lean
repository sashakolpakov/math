import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveBochner.LowerBound
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.CutoffIntegrability

/-! # Bochner Cutoff Lower Bound -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The original Bochner pairing and the native rough integral give the exact squared-cutoff Laplacian lower bound. -/

open _root_.MeasureTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

def HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveBochnerCutoffLowerBound
    (η : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (c : ℝ) : Prop :=
  ∀ a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1,
    c * (∫ z, h.projectiveGlobalPair V e 1 a.val a.val z * SquaredRealCutoff.squaredRealCutoff η z).re -
        (∫ z, h.projectiveGlobalPair V e 1 a.val a.val z * (Projective.CutoffEnergy.projectiveCutoffEnergy V e η z : ℂ)).re ≤
      (∫ z, h.projectiveGlobalPair V e 1 (h.smoothDolbeaultLaplacianOne V a) a.val z * SquaredRealCutoff.squaredRealCutoff η z).re

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveBochnerPairLowerBound_cutoff
    (η : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (c : ℝ)
    (hB : h.projectiveBochnerPairLowerBound V e (tsupport η) c)
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    c * (h.projectiveGlobalPair V e 1 a.val a.val z * SquaredRealCutoff.squaredRealCutoff η z).re ≤
      (h.projectiveGlobalPair V e 1 (h.smoothDolbeaultLaplacianOne V a) a.val z * SquaredRealCutoff.squaredRealCutoff η z).re -
        (h.projectiveRoughPair V e ⊤ 1 a.val a.val z * SquaredRealCutoff.squaredRealCutoff η z).re := by
  by_cases hz : z ∈ tsupport η
  · have hp := mul_le_mul_of_nonneg_right (hB a z hz) (sq_nonneg (η z))
    rw [Complex.sub_re] at hp
    simp only [Complex.mul_re, SquaredRealCutoff.squaredRealCutoff_re, SquaredRealCutoff.squaredRealCutoff_im, mul_zero, sub_zero]
    nlinarith only [hp]
  · have hχ : SquaredRealCutoff.squaredRealCutoff η z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht => hz (SquaredRealCutoff.squaredRealCutoff_tsupport η ht))
    simp only [hχ, mul_zero, Complex.zero_re, sub_zero, le_refl]

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveBochnerCutoffLowerBound_of_pair
    (η : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (c : ℝ)
    (hB : h.projectiveBochnerPairLowerBound V e (tsupport η) c) :
    h.projectiveBochnerCutoffLowerBound V e η c := by
  intro a
  have hχ := SquaredRealCutoff.squaredRealCutoff_smooth η hη
  have hχc := SquaredRealCutoff.squaredRealCutoff_hasCompactSupport η hc
  have hχs := (SquaredRealCutoff.squaredRealCutoff_tsupport η).trans hs
  have hP := h.projectiveGlobalPair_cutoff_integrable V e he 1 a.val a.val (SquaredRealCutoff.squaredRealCutoff η) hχ hχc hχs
  have hL := h.projectiveGlobalPair_cutoff_integrable V e he 1
    (h.smoothDolbeaultLaplacianOne V a) a.val (SquaredRealCutoff.squaredRealCutoff η) hχ hχc hχs
  have hR := h.projectiveRoughPair_cutoff_integrable V e he ⊤ 1 a.val a.val (SquaredRealCutoff.squaredRealCutoff η) hχ hχc
    (fun _ hz => ⟨hχs hz, trivial⟩)
  have hi := integral_mono (hP.re.const_mul c) (hL.re.sub hR.re)
    (h.projectiveBochnerPairLowerBound_cutoff V e η c hB a)
  simp only [Pi.sub_apply] at hi
  rw [integral_const_mul, integral_sub hL.re hR.re, integral_re hP, integral_re hL, integral_re hR] at hi
  change c * (∫ z, h.projectiveGlobalPair V e 1 a.val a.val z * SquaredRealCutoff.squaredRealCutoff η z).re ≤
    (∫ z, h.projectiveGlobalPair V e 1 (h.smoothDolbeaultLaplacianOne V a) a.val z * SquaredRealCutoff.squaredRealCutoff η z).re -
      (∫ z, h.projectiveRoughPair V e ⊤ 1 a.val a.val z * SquaredRealCutoff.squaredRealCutoff η z).re at hi
  have hr := h.projectiveSquaredCutoff_rough_lower_bound V e he 1 a.val η hη hc hs
  linarith only [hi, hr]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
