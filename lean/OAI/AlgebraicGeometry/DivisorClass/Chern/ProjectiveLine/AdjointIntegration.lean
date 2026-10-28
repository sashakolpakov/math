import OAI.AlgebraicGeometry.DivisorClass.Chern.FirstOrderConnectionIntegration
import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveLine.AdjointCoefficients

/-! # Adjoint Integration -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Actual local line-connection integration by parts on the original projective chart domains. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

def HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveCovariantCoordinateDerivative (i : V.analyticSpace) (n : ℕ)
    (a : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n)
    (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1) :=
  Analysis.HodgeTheory.Decomposition.LocalAdjoint.Constructions.firstOrderCoordinateOperator (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.projectiveEuclideanExteriorSymbol V n) a z +
    Line.ConnectionOperator.lineConnectionCoordinateOperator (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
      (h.projectiveConnectionChart V e i z) (a z)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveCovariantAdjointCoefficients_weighted (i : V.analyticSpace) (n : ℕ)
    (a : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    h.projectiveWeightedFormOperator V e i n z (h.projectiveCovariantAdjointCoefficients V e i n a z) =
      h.projectiveCovariantAdjointNumerator V e i n a z :=
  (h.projectiveWeightedFormOperator_isInvertible V e he i n hz).self_apply_inverse _

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveCovariantAdjointCoefficients_integration (i : V.analyticSpace) (n : ℕ)
    (a : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n)
    (b : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))
    (ha : ContDiff ℝ ∞ a) (hb : ContDiffOn ℝ ∞ b
      (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) : Set _))
    (hac : HasCompactSupport a)
    (hs : tsupport a ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    (∫ z, inner ℝ (h.projectiveWeightedFormOperator V e i (n + 1) z (b z))
      (h.projectiveCovariantCoordinateDerivative V e i n a z)) =
      ∫ z, inner ℝ (h.projectiveWeightedFormOperator V e i n z
        (h.projectiveCovariantAdjointCoefficients V e i n b z)) (a z) := by
  have hd : (∫ z, inner ℝ (h.projectiveWeightedFormOperator V e i (n + 1) z (b z))
      (h.projectiveCovariantCoordinateDerivative V e i n a z)) =
      ∫ z, inner ℝ (h.projectiveCovariantAdjointNumerator V e i n b z) (a z) :=
    FirstOrderConnectionIntegration.firstOrderConnection_integration_on volume (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
      (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.projectiveEuclideanExteriorSymbol V n) (h.projectiveWeightedFormOperator V e i (n + 1))
      (fun z => Line.ConnectionOperator.lineConnectionCoordinateOperator (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
        (h.projectiveConnectionChart V e i z))
      (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen
      (h.projectiveWeightedFormOperator_smooth V e he i (n + 1))
      (Line.ConnectionOperator.lineConnectionCoordinateOperator_smoothOn (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
        (h.projectiveConnectionChart V e i) (h.projectiveConnectionChart_smooth V e he i)) a b ha hb hac hs
  rw [hd]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  change inner ℝ (h.projectiveCovariantAdjointNumerator V e i n b z) (a z) =
    inner ℝ (h.projectiveWeightedFormOperator V e i n z (h.projectiveCovariantAdjointCoefficients V e i n b z)) (a z)
  by_cases hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
  · rw [h.projectiveCovariantAdjointCoefficients_weighted V e he i n b hz]
  · have ha0 : a z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hs h))
    rw [ha0, inner_zero_right, inner_zero_right]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
