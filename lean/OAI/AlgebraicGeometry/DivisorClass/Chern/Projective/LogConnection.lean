import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.BasePartition

/-! # Log Connection -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The original logarithmic line-connection transition law in literal projective coordinates. -/

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

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveConnectionChart_log_overlap (i j : V.analyticSpace)
    (W : Opens V.analyticSpace)
    (hW : W ≤ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i ⊓
      Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u j)
    (l : Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel) (M := W))
    (hl : ∀ x : W, (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition V.analyticModel V.analyticSpace u i j).val
      ⟨x.val, hW x.property⟩ = Complex.exp (l x))
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e W) (v : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    h.projectiveConnectionChart V e i z v = h.projectiveConnectionChart V e j z v +
      fderiv ℝ (Projective.BasePartition.projectiveScalarChart V e W (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen l)) z v := by
  have hd := congrArg (fun a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel W 1 =>
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 a.extension z (fun _ => v)) (h.localConnection_log_overlap i j W hW l hl)
  rw [ZeroConnectionChart.projectiveOpenChartForm_add V e W 1 _ _ z,
    Projective.BasePartition.projectiveOpenChartForm_restrict V e (hW.trans inf_le_left) 1 (h.localConnection i) hz,
    Projective.BasePartition.projectiveOpenChartForm_restrict V e (hW.trans inf_le_right) 1 (h.localConnection j) hz] at hd
  simp only [ContinuousAlternatingMap.add_apply] at hd
  have hs := Projective.BasePartition.projectiveScalarChart_derivative V e he W (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen l) hz v
  rw [AntiOneFormCoordinates.oneFormLinear_apply] at hs
  rw [hs] at hd
  exact hd

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
