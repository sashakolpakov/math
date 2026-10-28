import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.GlobalCovariantAdjoint
import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveLine.KahlerAdjoint

/-! # Intrinsic Kahler Adjoint -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The Kähler identity has the literal original global Dolbeault adjoint as its right-hand side. -/

open _root_.TopologicalSpace Filter
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (i : V.analyticSpace)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveCovariantAdjointCoefficients_congr (n : ℕ)
    (a b : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hab : a =ᶠ[𝓝 z] b) :
    h.projectiveCovariantAdjointCoefficients V e i n a z = h.projectiveCovariantAdjointCoefficients V e i n b z := by
  have hi (j : Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) :
      (fun y => (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.projectiveEuclideanExteriorSymbol V n j).adjoint (h.projectiveWeightedFormOperator V e i (n + 1) y (a y))) =ᶠ[𝓝 z]
      (fun y => (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.projectiveEuclideanExteriorSymbol V n j).adjoint (h.projectiveWeightedFormOperator V e i (n + 1) y (b y))) := by
    filter_upwards [hab] with y hy
    rw [hy]
  unfold HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveCovariantAdjointCoefficients HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveCovariantAdjointNumerator Analysis.HodgeTheory.Decomposition.LocalAdjoint.Constructions.formalAdjointNumerator
  simp_rw [(hi _).fderiv_eq]
  rw [hab.eq_of_nhds]

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.degreeCodifferential_componentCoefficients
    (b : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e 0 ((h.degreeCodifferential V 0 b.val).val i).extension z =
      h.projectiveCovariantAdjointCoefficients V e i 0 (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e 1 (b.val.val i).extension) z := by
  have heq : Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e 1 (Holomorphic.GlobalFrameForms.holomorphicLineGlobalFrame u i 1 b.val).extension =ᶠ[𝓝 z]
      Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e 1 (b.val.val i).extension := by
    filter_upwards [(ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen.mem_nhds hz] with y hy
    exact Holomorphic.ChartTestDerivatives.holomorphicLineGlobalFrame_coefficients V e i 1 b.val hy
  exact (Holomorphic.ChartTestDerivatives.holomorphicLineGlobalFrame_coefficients V e i 0 (h.degreeCodifferential V 0 b.val) hz).symm.trans
    ((h.degreeCodifferential_chartCoefficients V e he i b hz).trans
      (h.projectiveCovariantAdjointCoefficients_congr V e i 0 _ _ heq))

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveKahler_globalDolbeaultAdjoint
    (b : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 0
      (Analysis.HodgeTheory.Decomposition.LefschetzSymbol.Constructions.metricLefschetzContraction 0 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z)
        (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
        (Line.ConnectionSymbols.lineTwistedExteriorDerivative 1 (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)
          (h.projectiveConnectionChart V e i) (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (b.val.val i).extension) z)) =
      Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e 0 ((h.degreeCodifferential V 0 b.val).val i).extension z :=
  (h.projectiveKahler_adjoint_zero V e he ⊤ b.val i
    (show z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (⊤ ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
      from ⟨hz.1, trivial, hz.2⟩)).trans (h.degreeCodifferential_componentCoefficients V e he i b hz).symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
