import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.CutoffEnergy
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.GlobalPairSmooth
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.GluedIntegration

/-! # Cutoff Integrability -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

section

/-! Every term of the squared base-cutoff estimate is integrable for the original bundle metric. -/

open _root_.MeasureTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

def HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveSquaredCutoffIntegrand (n : ℕ)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (η : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : ℂ :=
  h.projectiveTensorPair V e ⊤ n a a z * SquaredRealCutoff.squaredRealCutoff η z +
    ∑ k, h.projectiveTensorFlux V e ⊤ n a a k z *
      fderiv ℝ (SquaredRealCutoff.squaredRealCutoff η) z ((stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) k)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveCutoffErrorPair_integrable (n : ℕ)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (η : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    Integrable (fun z => h.projectiveGlobalPair V e n a a z * (Projective.CutoffEnergy.projectiveCutoffEnergy V e η z : ℂ)) := by
  have hE := Projective.CutoffEnergy.projectiveCutoffEnergy_smooth V e he η hη hs
  have hEc := Projective.CutoffEnergy.projectiveCutoffEnergy_hasCompactSupport V e η hc
  exact h.projectiveGlobalPair_cutoff_integrable V e he n a a _
    (Complex.ofRealCLM.contDiff.comp hE) (hEc.comp_left Complex.ofReal_zero)
    ((tsupport_comp_subset Complex.ofReal_zero (Projective.CutoffEnergy.projectiveCutoffEnergy V e η)).trans
      ((Projective.CutoffEnergy.projectiveCutoffEnergy_tsupport V e η).trans hs))

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveSquaredCutoffTensor_integrable (n : ℕ)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (η : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    Integrable (fun z => h.projectiveTensorPair V e ⊤ n a a z * SquaredRealCutoff.squaredRealCutoff η z) :=
  h.projectiveTensorPair_cutoff_integrable V e he ⊤ n a a (SquaredRealCutoff.squaredRealCutoff η)
    (SquaredRealCutoff.squaredRealCutoff_smooth η hη) (SquaredRealCutoff.squaredRealCutoff_hasCompactSupport η hc)
    (fun _ hz => ⟨hs (SquaredRealCutoff.squaredRealCutoff_tsupport η hz), trivial⟩)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveSquaredCutoffFlux_integrable (n : ℕ)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (η : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (k : Fin (Module.finrank ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) :
    Integrable (fun z => h.projectiveTensorFlux V e ⊤ n a a k z *
      fderiv ℝ (SquaredRealCutoff.squaredRealCutoff η) z ((stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) k)) := by
  have hF : ContDiffOn ℝ ∞ (h.projectiveTensorFlux V e ⊤ n a a k) (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _) :=
    (h.projectiveTensorFlux_smooth V e he ⊤ n a a k).mono (fun _ hz => ⟨hz, trivial⟩)
  exact ComplexMultiplication.HodgeComparison.HolomorphicIntegrationByParts.CM.Construction.smooth_mul_test_integrable volume _ _ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen hF
    (Analysis.HodgeTheory.Decomposition.LocalAdjoint.Constructions.smooth_directional_derivative (SquaredRealCutoff.squaredRealCutoff η) (SquaredRealCutoff.squaredRealCutoff_smooth η hη) _)
    ((SquaredRealCutoff.squaredRealCutoff_hasCompactSupport η hc).fderiv_apply ℝ _)
    ((tsupport_fderiv_apply_subset ℝ _).trans ((SquaredRealCutoff.squaredRealCutoff_tsupport η).trans hs))

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveSquaredCutoffIntegrand_integrable (n : ℕ)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (η : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    Integrable (h.projectiveSquaredCutoffIntegrand V e n a η) :=
  (h.projectiveSquaredCutoffTensor_integrable V e he n a η hη hc hs).add
    (integrable_finsetSum Finset.univ (fun k _ => h.projectiveSquaredCutoffFlux_integrable V e he n a η hη hc hs k))

end

/-! The native rough Laplacian paired against a squared base cutoff is bounded below by its actual cutoff error integral. -/

open _root_.MeasureTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveSquaredCutoff_rough_integral (n : ℕ)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (η : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    (∫ z, h.projectiveRoughPair V e ⊤ n a a z * SquaredRealCutoff.squaredRealCutoff η z) =
      ∫ z, h.projectiveSquaredCutoffIntegrand V e n a η z := by
  have hi := h.projectiveRoughPair_cutoff_integral V e he ⊤ n a a (SquaredRealCutoff.squaredRealCutoff η)
    (SquaredRealCutoff.squaredRealCutoff_smooth η hη) (SquaredRealCutoff.squaredRealCutoff_hasCompactSupport η hc)
    (fun _ hz => ⟨hs (SquaredRealCutoff.squaredRealCutoff_tsupport η hz), trivial⟩)
  rw [hi]
  unfold HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveSquaredCutoffIntegrand
  rw [integral_add (h.projectiveSquaredCutoffTensor_integrable V e he n a η hη hc hs)
      (integrable_finsetSum Finset.univ (fun k _ => h.projectiveSquaredCutoffFlux_integrable V e he n a η hη hc hs k)),
    integral_finsetSum Finset.univ (fun k _ => h.projectiveSquaredCutoffFlux_integrable V e he n a η hη hc hs k)]

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveSquaredCutoff_integrand_global_lower (n : ℕ)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (η : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ)
    (hη : ContDiff ℝ ∞ η) (hs : tsupport η ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    -(h.projectiveGlobalPair V e n a a z * (Projective.CutoffEnergy.projectiveCutoffEnergy V e η z : ℂ)).re ≤
      (h.projectiveSquaredCutoffIntegrand V e n a η z).re := by
  by_cases hz : z ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e
  · have hy := h.projectiveSquaredCutoff_integrand_lower_bound V e he n a η
      (hη.differentiable (by simp) z) hz
    simpa only [HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveSquaredCutoffIntegrand, Projective.CutoffEnergy.projectiveCutoffEnergy, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, neg_mul, mul_neg, mul_comm] using hy
  · have hnot : z ∉ tsupport η := fun ht => hz (hs ht)
    have hnotχ : z ∉ tsupport (SquaredRealCutoff.squaredRealCutoff η) := fun ht => hnot (SquaredRealCutoff.squaredRealCutoff_tsupport η ht)
    simp only [HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveSquaredCutoffIntegrand, Projective.CutoffEnergy.projectiveCutoffEnergy_zero V e η hnot,
      image_eq_zero_of_notMem_tsupport hnotχ, fderiv_of_notMem_tsupport ℝ hnotχ,
      Complex.ofReal_zero, zero_apply, mul_zero, Finset.sum_const_zero, add_zero,
      Complex.zero_re, neg_zero, le_refl]

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveSquaredCutoff_rough_lower_bound (n : ℕ)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (η : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    -(∫ z, h.projectiveGlobalPair V e n a a z * (Projective.CutoffEnergy.projectiveCutoffEnergy V e η z : ℂ)).re ≤
      (∫ z, h.projectiveRoughPair V e ⊤ n a a z * SquaredRealCutoff.squaredRealCutoff η z).re := by
  rw [h.projectiveSquaredCutoff_rough_integral V e he n a η hη hc hs]
  have hE := h.projectiveCutoffErrorPair_integrable V e he n a η hη hc hs
  have hI := h.projectiveSquaredCutoffIntegrand_integrable V e he n a η hη hc hs
  change -RCLike.re (∫ z, h.projectiveGlobalPair V e n a a z * (Projective.CutoffEnergy.projectiveCutoffEnergy V e η z : ℂ)) ≤
    RCLike.re (∫ z, h.projectiveSquaredCutoffIntegrand V e n a η z)
  rw [← integral_re hE, ← integral_re hI, ← integral_neg]
  exact integral_mono hE.re.neg hI.re
    (h.projectiveSquaredCutoff_integrand_global_lower V e he n a η hη hs)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
