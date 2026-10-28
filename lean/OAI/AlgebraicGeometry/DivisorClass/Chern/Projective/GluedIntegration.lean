import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.GluedDivergence

/-! # Glued Integration -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

section

/-! The native rough operator pairing is smooth after gluing all actual line frames in a fixed base chart. -/

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

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveRoughPair_eq_energy_sub_divergence
    (U : Opens V.analyticSpace) (n : ℕ) (a c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e U) :
    h.projectiveRoughPair V e U n a c z = h.projectiveTensorPair V e U n a c z -
      ∑ k, fderiv ℝ (h.projectiveTensorFlux V e U n a c k) z
        ((stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) k) := by
  rw [h.projectiveTensorFlux_divergence V e he U n a c hz]
  ring

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveRoughPair_smooth
    (U : Opens V.analyticSpace) (n : ℕ) (a c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n) :
    ContDiffOn ℝ ∞ (h.projectiveRoughPair V e U n a c) (ConnectionChartDerivative.projectiveOpenChartDomain V e U : Set _) := by
  have hd : ContDiffOn ℝ ∞ (fun z => ∑ k, fderiv ℝ (h.projectiveTensorFlux V e U n a c k) z
      ((stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) k)) (ConnectionChartDerivative.projectiveOpenChartDomain V e U : Set _) := by
    apply ContDiffOn.sum
    intro k _
    exact Analysis.HodgeTheory.Decomposition.LocalAdjointForm.Constructions.smoothOn_directional_derivative _ (ConnectionChartDerivative.projectiveOpenChartDomain V e U).isOpen
      (h.projectiveTensorFlux_smooth V e he U n a c k) _
  exact ((h.projectiveTensorPair_smooth V e he U n a c).sub hd).congr
    (fun _ hz => h.projectiveRoughPair_eq_energy_sub_divergence V e he U n a c hz)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveRoughPair_cutoff_integrable
    (U : Opens V.analyticSpace) (n : ℕ) (a c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n)
    (χ : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e U) :
    Integrable (fun z => h.projectiveRoughPair V e U n a c z * χ z) :=
  ComplexMultiplication.HodgeComparison.HolomorphicIntegrationByParts.CM.Construction.smooth_mul_test_integrable volume _ χ (ConnectionChartDerivative.projectiveOpenChartDomain V e U).isOpen
    (h.projectiveRoughPair_smooth V e he U n a c) hχ hc hs

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveTensorPair_cutoff_integrable
    (U : Opens V.analyticSpace) (n : ℕ) (a c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n)
    (χ : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e U) :
    Integrable (fun z => h.projectiveTensorPair V e U n a c z * χ z) :=
  ComplexMultiplication.HodgeComparison.HolomorphicIntegrationByParts.CM.Construction.smooth_mul_test_integrable volume _ χ (ConnectionChartDerivative.projectiveOpenChartDomain V e U).isOpen
    (h.projectiveTensorPair_smooth V e he U n a c) hχ hc hs

end

/-! Integration of the original rough pairing across all line frames, with only a fixed base-chart cutoff. -/

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

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveRoughPair_cutoff_integral
    (U : Opens V.analyticSpace) (n : ℕ) (a c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n)
    (χ : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e U) :
    (∫ z, h.projectiveRoughPair V e U n a c z * χ z) =
      (∫ z, h.projectiveTensorPair V e U n a c z * χ z) +
        ∑ k, ∫ z, h.projectiveTensorFlux V e U n a c k z *
          fderiv ℝ χ z ((stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) k) := by
  let D := ConnectionChartDerivative.projectiveOpenChartDomain V e U
  let b := stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
  let F := h.projectiveTensorFlux V e U n a c
  have hF (k : Fin (Module.finrank ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) : ContDiffOn ℝ ∞ (F k) (D : Set _) :=
    h.projectiveTensorFlux_smooth V e he U n a c k
  have hi (k : Fin (Module.finrank ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) :
      Integrable (fun z => fderiv ℝ (F k) z (b k) * χ z) :=
    ComplexMultiplication.HodgeComparison.HolomorphicIntegrationByParts.CM.Construction.smooth_mul_test_integrable volume _ χ D.isOpen
      (Analysis.HodgeTheory.Decomposition.LocalAdjointForm.Constructions.smoothOn_directional_derivative (F k) D.isOpen (hF k) (b k)) hχ hc hs
  have hP := h.projectiveTensorPair_cutoff_integrable V e he U n a c χ hχ hc hs
  have hp (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : h.projectiveRoughPair V e U n a c z * χ z =
      h.projectiveTensorPair V e U n a c z * χ z - ∑ k, fderiv ℝ (F k) z (b k) * χ z := by
    by_cases hz : z ∈ D
    · rw [h.projectiveRoughPair_eq_energy_sub_divergence V e he U n a c hz, sub_mul, Finset.sum_mul]
    · have hzχ : χ z = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hz (hs ht))
      simp only [hzχ, mul_zero, Finset.sum_const_zero, sub_zero]
  have hparts (k : Fin (Module.finrank ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) :
      (∫ z, fderiv ℝ (F k) z (b k) * χ z) = -(∫ z, F k z * fderiv ℝ χ z (b k)) := by
    have hv := ComplexMultiplication.HodgeComparison.HolomorphicIntegrationByParts.CM.Construction.integral_mul_directional_on volume (F k) χ D.isOpen (hF k) hχ hc hs (b k)
    simpa only [neg_neg] using congrArg Neg.neg hv.symm
  simp_rw [hp]
  rw [integral_sub hP (integrable_finsetSum Finset.univ (fun k _ => hi k)),
    integral_finsetSum Finset.univ (fun k _ => hi k)]
  simp_rw [hparts]
  rw [Finset.sum_neg_distrib, sub_neg_eq_add]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
