import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.TensorCutoff
import OAI.AlgebraicGeometry.DivisorClass.Chern.SquaredRealCutoff

/-! # Cutoff Energy -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.DivisorClass.Chern

/-! The actual squared-cutoff energy integrand is bounded below by the original inverse-metric cutoff error. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveSquaredCutoff_integrand_lower_bound (n : ℕ)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (η : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hη : DifferentiableAt ℝ η z) (hz : z ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    -fderiv ℝ η z (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (fderiv ℝ η z)) *
        (h.projectiveGlobalPair V e n a a z).re ≤
      (h.projectiveTensorPair V e ⊤ n a a z * SquaredRealCutoff.squaredRealCutoff η z +
        ∑ k, h.projectiveTensorFlux V e ⊤ n a a k z *
          fderiv ℝ (SquaredRealCutoff.squaredRealCutoff η) z ((stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) k)).re := by
  have hs : (∑ k, h.projectiveTensorFlux V e ⊤ n a a k z *
      fderiv ℝ (SquaredRealCutoff.squaredRealCutoff η) z ((stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) k)) =
      (2 * (η z : ℂ)) * ∑ k, h.projectiveTensorFlux V e ⊤ n a a k z *
        (fderiv ℝ η z ((stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) k) : ℂ) := by
    simp_rw [SquaredRealCutoff.squaredRealCutoff_fderiv η hη]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hs]
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, SquaredRealCutoff.squaredRealCutoff_re, SquaredRealCutoff.squaredRealCutoff_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat,
    mul_zero, zero_mul, add_zero, sub_zero]
  have hy := h.projectiveTensor_cutoff_lower_bound V e he n a (fderiv ℝ η z) (η z) hz
  simpa only [mul_comm] using hy

end AlgebraicGeometry.DivisorClass.Chern

namespace AlgebraicGeometry.DivisorClass.Chern.Projective.CutoffEnergy

/-! The actual inverse-metric cutoff error is smooth, compactly supported and bounded independently of every line metric. -/

open Filter
open scoped ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential.Constructions.metricDifferentialBilinearNormed Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential.Constructions.metricDifferentialBilinearNormedSpace

local instance cutoffEnergy_sharpNormed (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    NormedAddCommGroup ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ℝ) →L[ℝ] ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) := inferInstance
local instance cutoffEnergy_sharpSpace (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    NormedSpace ℝ ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ℝ) →L[ℝ] ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) := inferInstance

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

def projectiveCutoffEnergy (η : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : ℝ :=
  fderiv ℝ η z (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (fderiv ℝ η z))

theorem projectiveCutoffEnergy_zero (η : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∉ tsupport η) : projectiveCutoffEnergy V e η z = 0 := by
  rw [projectiveCutoffEnergy, fderiv_of_notMem_tsupport ℝ hz]
  rfl

theorem projectiveCutoffEnergy_tsupport (η : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) :
    tsupport (projectiveCutoffEnergy V e η) ⊆ tsupport η := by
  apply closure_minimal _ (isClosed_tsupport η)
  intro z hz
  by_contra hnot
  exact hz (projectiveCutoffEnergy_zero V e η hnot)

theorem projectiveCutoffEnergy_hasCompactSupport (η : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ)
    (hη : HasCompactSupport η) : HasCompactSupport (projectiveCutoffEnergy V e η) :=
  hη.isCompact.of_isClosed_subset (isClosed_tsupport _) (projectiveCutoffEnergy_tsupport V e η)

include he

theorem projectiveCutoffEnergy_nonneg (η : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    0 ≤ projectiveCutoffEnergy V e η z := by
  unfold projectiveCutoffEnergy
  rw [← Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp_pair (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z)
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz) (fderiv ℝ η z)]
  by_cases hzero : Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (fderiv ℝ η z) = 0
  · rw [hzero, map_zero]
  · exact (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz _ hzero).le

theorem projectiveCutoffEnergy_smoothOn (η : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hη : ContDiff ℝ ∞ η) :
    ContDiffOn ℝ ∞ (projectiveCutoffEnergy V e η) (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _) := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ η) (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _) :=
    hη.contDiffOn.fderiv_of_isOpen (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen (by simp)
  have hS := Analysis.HodgeTheory.Decomposition.KoszulSmooth.Constructions.bilinearMetricSharp_smoothOn (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e)
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he)
    (fun z hz => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz)
  exact hD.clm_apply (hS.clm_apply hD)

theorem projectiveCutoffEnergy_smooth (η : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hη : ContDiff ℝ ∞ η)
    (hs : tsupport η ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) : ContDiff ℝ ∞ (projectiveCutoffEnergy V e η) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e
  · exact (projectiveCutoffEnergy_smoothOn V e he η hη).contDiffAt ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)
  · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp
      (fun ht => hz (hs (projectiveCutoffEnergy_tsupport V e η ht))))

theorem projectiveCutoffEnergy_bound (η : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hη : ContDiff ℝ ∞ η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ∃ C : ℝ, 0 < C ∧ ∀ z, projectiveCutoffEnergy V e η z ≤ C := by
  have hE := projectiveCutoffEnergy_smooth V e he η hη hs
  obtain ⟨R, hR⟩ := hc.isCompact.bddAbove_image hE.continuous.continuousOn
  refine ⟨max R 0 + 1, by positivity, ?_⟩
  intro z
  by_cases hz : z ∈ tsupport η
  · exact (hR ⟨z, hz, rfl⟩).trans ((le_max_left R 0).trans (by linarith))
  · rw [projectiveCutoffEnergy_zero V e η hz]
    positivity

end AlgebraicGeometry.DivisorClass.Chern.Projective.CutoffEnergy

end

end OAI
