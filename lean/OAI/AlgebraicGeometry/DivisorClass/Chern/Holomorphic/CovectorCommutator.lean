import OAI.AlgebraicGeometry.DivisorClass.Chern.OneCovectorCurvature
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.ConnectionCurvature

/-! # Covector Commutator -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The commutator on original bundle one-forms has precisely the original line curvature and base curvature. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Line.CovectorConnectionOperator.lineOperator_formNormed Line.CovectorConnectionOperator.lineOperator_formSpace
  Line.CovectorConnectionOperator.lineOperator_endNormed Line.CovectorConnectionOperator.lineOperator_endSpace Line.CovectorConnectionOperator.lineOperator_directionNormed Line.CovectorConnectionOperator.lineOperator_directionSpace

theorem Holomorphic.CovectorCommutator.lineCovectorConnectionDerivative_commutator_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) {x : E}
    (hG : DifferentiableAt ℝ G x) (hA : DifferentiableAt ℝ A x) (ha : ContDiffAt ℝ ∞ a x)
    (v w : E) :
    Line.ConnectionSymbols.lineCovectorConnectionDerivative 1 G A (fun y => Line.ConnectionSymbols.lineCovectorConnectionDerivative 1 G A a y w) x v -
      Line.ConnectionSymbols.lineCovectorConnectionDerivative 1 G A (fun y => Line.ConnectionSymbols.lineCovectorConnectionDerivative 1 G A a y v) x w =
      -Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction 1 (OperatorConnectionCurvature.operatorConnectionCurvature G x v w) (a x) +
        (fderiv ℝ A x v w - fderiv ℝ A x w v) • a x := by
  simp_rw [Line.CovectorConnectionOperator.lineCovectorConnectionDerivative_operator]
  exact (OperatorConnectionCurvature.operatorConnectionDerivative_commutator _ a
    (Line.CovectorConnectionOperator.lineCovectorConnectionOperator_differentiableAt 1 G A hG hA) ha v w).trans
      (OneCovectorCurvature.lineCovectorConnectionCurvature_one G A hG hA v w (a x))

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

def Holomorphic.CovectorCommutator.projectiveBaseConnectionCurvature (z v w : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V :=
  OperatorConnectionCurvature.operatorConnectionCurvature (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) z v w

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveCovectorConnection_commutator
    (U : Opens V.analyticSpace) (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 1) (i : V.analyticSpace)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (v w : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    Line.ConnectionSymbols.lineCovectorConnectionDerivative 1 (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
      (fun y => Line.ConnectionSymbols.lineCovectorConnectionDerivative 1 (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
        (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val i).extension) y w) z v -
    Line.ConnectionSymbols.lineCovectorConnectionDerivative 1 (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
      (fun y => Line.ConnectionSymbols.lineCovectorConnectionDerivative 1 (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
        (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val i).extension) y v) z w =
      -Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction 1 (Holomorphic.CovectorCommutator.projectiveBaseConnectionCurvature V e z v w)
        (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val i).extension z) +
      Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 h.curvature.val z ![v, w] •
        Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val i).extension z := by
  have hzD : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) :=
    ⟨hz.1, hz.2.2⟩
  have hG := ((Analysis.HodgeTheory.Decomposition.ProjectiveConnectionSmooth.Constructions.projectiveConnectionCoefficient_smooth V e he).contDiffAt
    ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz.1)).differentiableAt (by simp)
  have hA := ((h.projectiveConnectionChart_smooth V e he i).contDiffAt
    ((ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen.mem_nhds hzD)).differentiableAt (by simp)
  have ha := (ConnectionChartDerivative.projectiveOpenChartForm_smooth V e he _ 1 (a.val i)).contDiffAt
    ((ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen.mem_nhds hz)
  rw [Holomorphic.CovectorCommutator.lineCovectorConnectionDerivative_commutator_one _ _ _ hG hA ha,
    h.projectiveConnectionChart_curvature V e he i hzD]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
