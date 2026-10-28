import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveLine.AdjointCoefficients

/-! # Kahler Adjoint -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The original bundle Kähler commutator equals the native smooth local matrix adjoint. -/

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

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveKahler_adjoint_zero (U : Opens V.analyticSpace)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 1) (i : V.analyticSpace) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 0
      (Analysis.HodgeTheory.Decomposition.LefschetzSymbol.Constructions.metricLefschetzContraction 0 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z)
        (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
        (Line.ConnectionSymbols.lineTwistedExteriorDerivative 1 (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)
          (h.projectiveConnectionChart V e i) (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val i).extension) z)) =
      h.projectiveCovariantAdjointCoefficients V e i 0 (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e 1 (a.val i).extension) z :=
  (congrArg (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 0)
    (h.projectiveKahler_zero V e he U a i hz)).trans
      (h.projectiveCovariantAdjointCoefficients_eq V e he 0 U a i hz).symm

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveKahler_adjoint (n : ℕ) (U : Opens V.analyticSpace)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U (n + 1 + 1)) (i : V.analyticSpace) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis (n + 1)
      (Analysis.HodgeTheory.Decomposition.LefschetzSymbol.Constructions.metricLefschetzContraction (n + 1) (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z)
          (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
          (Line.ConnectionSymbols.lineTwistedExteriorDerivative (n + 1 + 1) (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)
            (h.projectiveConnectionChart V e i) (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e (n + 1 + 1) (a.val i).extension) z) -
        Line.ConnectionSymbols.lineTwistedExteriorDerivative n (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) (h.projectiveConnectionChart V e i)
          (fun y => Analysis.HodgeTheory.Decomposition.LefschetzSymbol.Constructions.metricLefschetzContraction n (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e y)
            (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
            (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e (n + 1 + 1) (a.val i).extension y)) z) =
      h.projectiveCovariantAdjointCoefficients V e i (n + 1)
        (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e (n + 1 + 1) (a.val i).extension) z :=
  (congrArg (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis (n + 1))
    (h.projectiveKahler V e he n U a i hz)).trans
      (h.projectiveCovariantAdjointCoefficients_eq V e he (n + 1) U a i hz).symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
