import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.MetricPointEstimate
import OAI.AlgebraicGeometry.DivisorClass.Chern.PointLogMetricSolver

/-! # Point Log Metric Evaluation -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.PointLogMetricEvaluation

noncomputable section

/-! Fully constructed original logarithmic point metrics give a quantitative evaluation estimate on a fixed local frame neighborhood. -/

open _root_.MeasureTheory _root_.Metric Set
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem projectivePointLogMetric_evaluation (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) (i : V.analyticSpace)
    (x : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
    (hx : x ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    ∃ R c : ℝ, 0 < R ∧ 0 < c ∧
      closedBall x R ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) ∧
      ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ R ^ 2 → ∀ a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0,
      DiffContOnCl ℂ (Holomorphic.ZeroChartPair.holomorphicLineZeroChart V e i a) (ball x (Real.sqrt ε)) →
      c * ((volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).real (ball 0 1) *
        ‖Holomorphic.ZeroChartPair.holomorphicLineZeroChart V e i a x‖ ^ 2) ≤
        2 ^ (V.complexDimension + 1) * ε *
          ((h.withPotential (PointLogMetricSolver.projectivePointLogPotential V e he x hx.1 (V.complexDimension + 1) ε hε)).formIntegralPair V 0 a a).re := by
  have H := PointLogMetricSolver.projectivePointLogPotential_uniform_neighborhood V e he x hx.1
  let R0 := H.choose
  have hR0 : 0 < R0 := H.choose_spec.1
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp
    ((ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen.mem_nhds hx)
  let R := min R0 (r / 2)
  have hR : 0 < R := lt_min hR0 (half_pos hr)
  have hK : closedBall x R ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) :=
    ((closedBall_subset_closedBall (min_le_right R0 (r / 2))).trans
      (closedBall_subset_ball (half_lt_self hr))).trans hb
  have HC := h.logarithmic_metric_point_estimate V e he i (isCompact_closedBall x R) hK
  let c := HC.choose
  have hc : 0 < c := HC.choose_spec.1
  refine ⟨R, c, hR, hc, hK, fun ε hε hεR a ha => ?_⟩
  have hsqrt : Real.sqrt ε ≤ R := (Real.sqrt_le_iff).mpr ⟨hR.le, hεR⟩
  have hball : ball x (Real.sqrt ε) ⊆ closedBall x R :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall hsqrt)
  apply HC.choose_spec.2 x ε hε _ a hball ha
  intro z hz
  exact H.choose_spec.2.2 (V.complexDimension + 1) ε hε z
    ((closedBall_subset_closedBall (min_le_left R0 (r / 2))) (hball hz))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.PointLogMetricEvaluation
