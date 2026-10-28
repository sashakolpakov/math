import OAI.AlgebraicGeometry.DivisorClass.Chern.TensorMetricUniformLower
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.Energy

/-! # Energy Lower -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Uniform control of full covariant derivatives by the actual projective bundle energy on compact chart sets. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveTensorMetric_uniform_lower (n : ℕ) (i : V.analyticSpace)
    {T : Set (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hT : IsCompact T)
    (hs : T ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    ∃ c : ℝ, 0 < c ∧ ∀ z ∈ T, ∀ N : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) n,
      c * ‖N‖ ^ 2 ≤ ((ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z : ℂ) * h.projectiveWeightChart V e i z *
        CovectorTensorAlgebra.covectorTensorMetricPair (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) N N).re := by
  obtain ⟨c, hc, hb⟩ := TensorMetricUniformLower.covectorTensorMetricPair_uniform_lower
    (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e)
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he)
    (fun _ hz => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he hz)
    (fun _ hz => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz) hT (fun _ hz => (hs hz).1)
  let q := fun z => ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z * (h.projectiveWeightChart V e i z).re
  have hq : ContinuousOn q T :=
    (((ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity_smooth V e he).continuousOn.mono (fun _ hz => (hs hz).1))).mul
      (Complex.continuous_re.comp_continuousOn ((h.projectiveWeightChart_smooth V e he i).continuousOn.mono hs))
  obtain ⟨d, hd, hdb⟩ := hT.exists_forall_le' hq (a := (0 : ℝ)) (by
    intro z hz
    dsimp only [q]
    rw [h.projectiveWeightChart_apply V e i (hs hz), Complex.ofReal_re]
    exact mul_pos (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity_pos V e he (hs hz).1) (h.positive i _))
  refine ⟨d * c, mul_pos hd hc, fun z hz N => ?_⟩
  have hnon := CovectorTensorAlgebra.covectorTensorMetricPair_nonneg
    (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z)
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he (hs hz).1) (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he (hs hz).1) N
  have hl := (mul_le_mul_of_nonneg_left (hb z hz N) hd.le).trans
    (mul_le_mul_of_nonneg_right (hdb z hz) hnon)
  rw [h.projectiveWeightChart_apply V e i (hs hz)]
  dsimp only [q] at hl
  rw [h.projectiveWeightChart_apply V e i (hs hz), Complex.ofReal_re] at hl
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, add_zero, sub_zero]
  simpa only [mul_assoc] using hl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
