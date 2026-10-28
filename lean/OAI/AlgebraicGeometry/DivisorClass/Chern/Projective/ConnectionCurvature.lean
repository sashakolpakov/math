import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveLine.AdjointCoefficients
import OAI.AlgebraicGeometry.DivisorClass.Chern.ScalarOneFormDerivative
import OAI.Analysis.HodgeTheory.Decomposition.ProjectiveConnectionSmooth

/-! # Connection Curvature -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The derivative of the original coordinate line connection is the original global curvature. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.ProjectiveConnectionSmooth.Constructions

theorem Projective.ConnectionCurvature.oneFormLinear_fderiv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) {x : E} (ha : DifferentiableAt ℝ a x) (v : E) :
    fderiv ℝ (fun y => AntiOneFormCoordinates.oneFormLinear (a y)) x v = AntiOneFormCoordinates.oneFormLinear (fderiv ℝ a x v) := by
  have hd := ((AntiOneFormCoordinates.oneFormLinearEquiv (E := E)).symm.toContinuousLinearMap.hasFDerivAt.comp x ha.hasFDerivAt).fderiv
  exact congrArg (fun T => T v) hd

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

omit he in
theorem Projective.ConnectionCurvature.projectiveOpenChartForm_onOpen (U : Opens V.analyticSpace) (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e U) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen U a).extension z =
      Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n a.val z := by
  unfold Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart
  rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply _ ⟨e.symm (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z), hz.2⟩]
  rfl

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveConnectionChart_curvature (i : V.analyticSpace)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (v w : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    fderiv ℝ (h.projectiveConnectionChart V e i) z v w -
      fderiv ℝ (h.projectiveConnectionChart V e i) z w v =
      Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 h.curvature.val z ![v, w] := by
  let D := Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i
  have ha := ((ConnectionChartDerivative.projectiveOpenChartForm_smooth V e he D 1 (h.localConnection i)).contDiffAt
    ((ConnectionChartDerivative.projectiveOpenChartDomain V e D).isOpen.mem_nhds hz)).differentiableAt (by simp)
  have hc := congrArg (fun a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel D 2 =>
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 a.extension z ![v, w]) ((h.localConnection_d i).trans (h.curvature_onOpen i).symm)
  rw [ConnectionChartDerivative.projectiveOpenChartForm_d V e he D 1 (h.localConnection i) hz,
    Projective.ConnectionCurvature.projectiveOpenChartForm_onOpen V e D 2 h.curvature hz, ScalarOneFormDerivative.extDeriv_one_apply] at hc
  unfold HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveConnectionChart
  rw [Projective.ConnectionCurvature.oneFormLinear_fderiv _ ha v, Projective.ConnectionCurvature.oneFormLinear_fderiv _ ha w]
  exact hc

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
