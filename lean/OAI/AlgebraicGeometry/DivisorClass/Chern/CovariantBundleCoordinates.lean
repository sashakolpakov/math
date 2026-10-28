import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveLine.AdjointIntegration
import OAI.AlgebraicGeometry.DivisorClass.Chern.ZeroConnectionChart
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CovariantCurvature

/-! # Covariant Bundle Coordinates -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Native coordinate operators preserve the literal original bundle covariant derivatives. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section Coordinates
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

theorem CovariantBundleCoordinates.lineExteriorDerivative_coordinates (b : Module.Basis ι ℝ E) (n : ℕ)
    (A : E → E →L[ℝ] ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x : E) (ha : DifferentiableAt ℝ a x) :
    Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b (n + 1) (Line.ConnectionSymbols.lineExteriorDerivative n A a x) =
      Analysis.HodgeTheory.Decomposition.LocalAdjoint.Constructions.firstOrderCoordinateOperator b (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.coordinateExteriorSymbol b n) (fun y => Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n (a y)) x +
        Line.ConnectionOperator.lineConnectionCoordinateOperator b n (A x) (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n (a x)) := by
  rw [Line.ConnectionSymbols.lineExteriorDerivative, map_add, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorDerivative_in_coordinates b n a x ha,
    Line.ConnectionOperator.lineConnectionCoordinateOperator_apply]
end Coordinates

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.covariantDerivative_coordinates (U : Opens V.analyticSpace)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 0) (i : V.analyticSpace) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    h.projectiveCovariantCoordinateDerivative V e i 0 (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e 0 (a.val i).extension) z =
      Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e 1 ((h.covariantDerivative U a).val i).extension z := by
  let W := U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i
  let A : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel W 1 := Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict inf_le_right (h.localConnection i)
  let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
  have ha := ((ConnectionChartDerivative.projectiveOpenChartForm_smooth V e he W 0 (a.val i)).contDiffAt
    ((ConnectionChartDerivative.projectiveOpenChartDomain V e W).isOpen.mem_nhds hz)).differentiableAt (by simp)
  have hc : AntiOneFormCoordinates.oneFormLinear (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 A.extension z) = h.projectiveConnectionChart V e i z := by
    unfold A HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveConnectionChart Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm
    rw [Open.ManifoldBidegree.openManifold_restrict_inChart inf_le_right (h.localConnection i) e hz.2]
  have hd := CovariantBundleCoordinates.lineExteriorDerivative_coordinates b 0
    (fun y => AntiOneFormCoordinates.oneFormLinear (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 A.extension y))
    (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 0 (a.val i).extension) z ha
  rw [hc] at hd
  change h.projectiveCovariantCoordinateDerivative V e i 0
    (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e 0 (a.val i).extension) z =
      Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b 1 (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (SmoothScalarExterior.openConnectionDerivative A (a.val i)).extension z)
  exact hd.symm.trans (congrArg (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b 1)
    (ZeroConnectionChart.projectiveOpenChartForm_connectionZero V e he W A (a.val i) hz).symm)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.covariantDerivativeOne_coordinates (U : Opens V.analyticSpace)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 1) (i : V.analyticSpace) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    h.projectiveCovariantCoordinateDerivative V e i 1 (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e 1 (a.val i).extension) z =
      Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e 2 ((h.covariantDerivativeOne U a).val i).extension z := by
  let W := U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i
  let A : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel W 1 := Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict inf_le_right (h.localConnection i)
  let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
  have ha := ((ConnectionChartDerivative.projectiveOpenChartForm_smooth V e he W 1 (a.val i)).contDiffAt
    ((ConnectionChartDerivative.projectiveOpenChartDomain V e W).isOpen.mem_nhds hz)).differentiableAt (by simp)
  have hc : AntiOneFormCoordinates.oneFormLinear (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 A.extension z) = h.projectiveConnectionChart V e i z := by
    unfold A HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveConnectionChart Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm
    rw [Open.ManifoldBidegree.openManifold_restrict_inChart inf_le_right (h.localConnection i) e hz.2]
  have hd := CovariantBundleCoordinates.lineExteriorDerivative_coordinates b 1
    (fun y => AntiOneFormCoordinates.oneFormLinear (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 A.extension y))
    (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val i).extension) z ha
  rw [hc] at hd
  change h.projectiveCovariantCoordinateDerivative V e i 1
    (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e 1 (a.val i).extension) z =
      Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b 2 (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 (Open.ConnectionCurvature.openConnectionDerivativeOne A (a.val i)).extension z)
  exact hd.symm.trans (congrArg (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b 2)
    (ConnectionChartDerivative.projectiveOpenChartForm_connectionOne V e he W A (a.val i) hz).symm)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
