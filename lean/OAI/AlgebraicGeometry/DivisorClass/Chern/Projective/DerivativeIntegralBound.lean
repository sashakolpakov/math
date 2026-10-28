import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.DerivativeIntegral
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.CovariantIntegralBound

/-! # Derivative Integral Bound -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Ordinary directional derivative bounds for compact fields in an original projective line frame. -/

open _root_.MeasureTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Line.HessianBilinear.tensorConnection_formNormed Line.HessianBilinear.tensorConnection_formSpace
  Line.HessianBilinear.tensorConnection_oneNormed Line.HessianBilinear.tensorConnection_oneSpace
  Line.CovectorConnectionOperator.lineOperator_endNormed Line.CovectorConnectionOperator.lineOperator_endSpace Line.CovectorConnectionOperator.lineOperator_directionNormed Line.CovectorConnectionOperator.lineOperator_directionSpace

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)

def Projective.DerivativeIntegralBound.projectiveFieldNormIntegral (n : ℕ)
    (a : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) n) : ℝ := ∫ z, ‖a z‖ ^ 2

def Projective.DerivativeIntegralBound.projectiveFieldDirectionalIntegral (n : ℕ)
    (a : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) n) (v : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : ℝ :=
  ∫ z, ‖fderiv ℝ a z v‖ ^ 2

include he in
theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveOrdinaryDerivative_integral_bound (n : ℕ) (i : V.analyticSpace)
    {T : Set (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hT : IsCompact T)
    (hTD : T ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ (a : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) n),
      ContDiff ℝ ∞ a → HasCompactSupport a → tsupport a ⊆ T →
      ∀ v : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ‖v‖ = 1 →
        Projective.DerivativeIntegralBound.projectiveFieldDirectionalIntegral V n a v ≤
          C * h.projectiveFullEnergyIntegral V e n i a + D * Projective.DerivativeIntegralBound.projectiveFieldNormIntegral V n a := by
  let U := ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
  have hG : ContDiffOn ℝ ∞ (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) U :=
    (Analysis.HodgeTheory.Decomposition.ProjectiveConnectionSmooth.Constructions.projectiveConnectionCoefficient_smooth V e he).mono (fun _ hz => hz.1)
  have hA := h.projectiveConnectionChart_smooth V e he i
  obtain ⟨C, hC, hCov⟩ := h.projectiveCovariantDerivative_integral_bound V e he n i hT hTD
  obtain ⟨K, hK, hKb⟩ := Line.CovectorConnectionOperator.lineCovectorConnectionOperator_bound n
    (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i) hG hA hT hTD
  refine ⟨2 * C, 2 * K ^ 2, by positivity, by positivity, fun a ha hac hs v hv => ?_⟩
  have hp := Line.DerivativeIntegral.lineCovectorDerivative_direction_integral volume n
    (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i) a U.isOpen hG hA ha hac hs hTD hK.le hKb v hv
  have hn := hCov a ha hac hs
  calc
    _ ≤ 2 * h.projectiveCovariantNormIntegral V e n i a + (2 * K ^ 2) * Projective.DerivativeIntegralBound.projectiveFieldNormIntegral V n a := hp
    _ ≤ 2 * (C * h.projectiveFullEnergyIntegral V e n i a) + (2 * K ^ 2) * Projective.DerivativeIntegralBound.projectiveFieldNormIntegral V n a :=
      add_le_add (mul_le_mul_of_nonneg_left hn (by norm_num)) (le_refl _)
    _ = _ := by ring

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
