import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveLine.AdjointNumerator
import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.ConnectionOperator

/-! # Adjoint Coefficients -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Smooth native local adjoint coefficients, identified with the actual line covariant trace. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

def HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveCovariantAdjointCoefficients (i : V.analyticSpace) (n : ℕ)
    (a : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))
    (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n :=
  (h.projectiveWeightedFormOperator V e i n z).inverse (h.projectiveCovariantAdjointNumerator V e i n a z)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveCovariantAdjointCoefficients_eq (n : ℕ) (U : Opens V.analyticSpace)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U (n + 1)) (i : V.analyticSpace) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    h.projectiveCovariantAdjointCoefficients V e i n (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e (n + 1) (a.val i).extension) z =
      Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
        (Line.ConnectionSymbols.lineCovariantCodifferential (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
          (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e)
          (h.projectiveConnectionChart V e i) (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e (n + 1) (a.val i).extension) z) := by
  rw [HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveCovariantAdjointCoefficients, h.projectiveCovariantAdjointNumerator_eq V e he n U a i hz]
  exact (h.projectiveWeightedFormOperator_isInvertible V e he i n ⟨hz.1, hz.2.2⟩).inverse_apply_self _

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveConnectionChart_smooth (i : V.analyticSpace) :
    ContDiffOn ℝ ∞ (h.projectiveConnectionChart V e i)
      (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) : Set _) :=
  (AntiOneFormCoordinates.oneFormLinearEquiv (E := ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).symm.toContinuousLinearMap.contDiff.comp_contDiffOn
    (ConnectionChartDerivative.projectiveOpenChartForm_smooth V e he (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
      1 (h.localConnection i))

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveWeightedFormOperator_inverse_smooth (i : V.analyticSpace) (n : ℕ) :
    ContDiffOn ℝ ∞ (fun z => (h.projectiveWeightedFormOperator V e i n z).inverse)
      (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) : Set _) :=
  Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.inverseOperator_smoothOn _
    (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen
    (h.projectiveWeightedFormOperator_smooth V e he i n)
    (fun _ hz => h.projectiveWeightedFormOperator_isInvertible V e he i n hz)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveCovariantAdjointNumerator_smooth (i : V.analyticSpace) (n : ℕ)
    (a : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))
    (ha : ContDiffOn ℝ ∞ a
      (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) : Set _)) :
    ContDiffOn ℝ ∞ (h.projectiveCovariantAdjointNumerator V e i n a)
      (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) : Set _) := by
  have hfirst := Analysis.HodgeTheory.Decomposition.LocalAdjoint.Constructions.formalAdjointNumerator_smoothOn (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.projectiveEuclideanExteriorSymbol V n) (h.projectiveWeightedFormOperator V e i (n + 1)) a
    (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen
    (h.projectiveWeightedFormOperator_smooth V e he i (n + 1)) ha
  have hzero := (Line.ConnectionOperator.lineConnectionCoordinateAdjoint_smoothOn (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
    (h.projectiveConnectionChart V e i) (h.projectiveConnectionChart_smooth V e he i)).clm_apply
      ((h.projectiveWeightedFormOperator_smooth V e he i (n + 1)).clm_apply ha)
  exact hfirst.add hzero

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveCovariantAdjointCoefficients_smooth (i : V.analyticSpace) (n : ℕ)
    (a : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))
    (ha : ContDiffOn ℝ ∞ a
      (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) : Set _)) :
    ContDiffOn ℝ ∞ (h.projectiveCovariantAdjointCoefficients V e i n a)
      (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) : Set _) :=
  (h.projectiveWeightedFormOperator_inverse_smooth V e he i n).clm_apply
    (h.projectiveCovariantAdjointNumerator_smooth V e he i n a ha)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
