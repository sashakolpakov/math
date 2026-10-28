import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.EnergyLower
import OAI.AlgebraicGeometry.DivisorClass.Chern.CovariantNormIntegrability

/-! # Covariant Integral Bound -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The full original covariant derivative has a Euclidean L² bound from the actual full bundle energy. -/

open _root_.MeasureTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Line.HessianBilinear.tensorConnection_formNormed Line.HessianBilinear.tensorConnection_formSpace
  Line.HessianBilinear.tensorConnection_oneNormed Line.HessianBilinear.tensorConnection_oneSpace
  Line.RoughSmooth.roughSmooth_metricNormed Line.RoughSmooth.roughSmooth_metricSpace Line.RoughSmooth.roughSmooth_connectionNormed Line.RoughSmooth.roughSmooth_connectionSpace

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)

def HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveCovariantNormIntegral (n : ℕ) (i : V.analyticSpace)
    (a : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) n) : ℝ :=
  ∫ z, ‖Line.ConnectionSymbols.lineCovectorConnectionDerivative n (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e)
    (h.projectiveConnectionChart V e i) a z‖ ^ 2

def HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveFullEnergyIntegral (n : ℕ) (i : V.analyticSpace)
    (a : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) n) : ℝ :=
  (∫ z, Line.RoughDivergence.lineCovectorFullEnergy (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
    (h.projectiveWeightChart V e i) a z).re

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveCovariantDerivative_integral_bound (n : ℕ) (i : V.analyticSpace)
    {T : Set (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hT : IsCompact T)
    (hTD : T ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) n),
      ContDiff ℝ ∞ a → HasCompactSupport a → tsupport a ⊆ T →
      h.projectiveCovariantNormIntegral V e n i a ≤ C * h.projectiveFullEnergyIntegral V e n i a := by
  obtain ⟨c, hc, hb⟩ := h.projectiveTensorMetric_uniform_lower V e he n i hT hTD
  refine ⟨c⁻¹, inv_pos.mpr hc, fun a ha hac hs => ?_⟩
  let D := ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
  let M := Line.ConnectionSymbols.lineCovectorConnectionDerivative n (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i) a
  let E := Line.RoughDivergence.lineCovectorFullEnergy (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
    (h.projectiveWeightChart V e i) a
  have hi : Integrable (fun z => ‖M z‖ ^ 2) := CovariantNormIntegrability.lineCovectorConnectionDerivative_norm_sq_integrable volume n _ _ a D.isOpen
    ((Analysis.HodgeTheory.Decomposition.ProjectiveConnectionSmooth.Constructions.projectiveConnectionCoefficient_smooth V e he).mono (fun _ hz => hz.1))
    (h.projectiveConnectionChart_smooth V e he i) ha hac (hs.trans hTD)
  have hE : Integrable E := h.projectiveFullEnergy_integrable V e he n i a ha hac (hs.trans hTD)
  have hpoint (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : c * ‖M z‖ ^ 2 ≤ (E z).re :=
    CovariantNormIntegrability.lineCovectorFullEnergy_norm_lower_of_support (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
      (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
      (h.projectiveWeightChart V e i) a hs hb z
  have hint := integral_mono (hi.const_mul c) hE.re hpoint
  rw [integral_const_mul] at hint
  change c * (∫ z, ‖M z‖ ^ 2) ≤ ∫ z, (E z).re at hint
  have heq : (∫ z, (E z).re) = (∫ z, E z).re := integral_re hE
  rw [heq] at hint
  have hh := mul_le_mul_of_nonneg_left hint (inv_pos.mpr hc).le
  rwa [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] at hh

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
