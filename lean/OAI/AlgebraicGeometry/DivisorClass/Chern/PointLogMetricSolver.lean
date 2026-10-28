import OAI.AlgebraicGeometry.DivisorClass.Chern.PointLogCutoff
import OAI.AlgebraicGeometry.DivisorClass.Chern.Positive.LogPointCoercivity

/-! # Point Log Metric Solver -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.PointLogMetricSolver

noncomputable section

section

/-! Fully constructed actual point-logarithmic metric families and a single native smooth Dolbeault solver threshold, with no assumed cutoff or curvature-bound data. -/

open Filter
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (x : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hx : x ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (m : ℕ)

def projectivePointLogPotential (ε : ℝ) (hε : 0 < ε) : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0 :=
  Projective.LogPointPotential.projectiveLogPointPotential V e he (PointLogCutoff.projectivePointLogCutoff V e x hx)
    (PointLogCutoff.projectivePointLogCutoff_smooth V e x hx) (PointLogCutoff.projectivePointLogCutoff_compact V e x hx)
    (PointLogCutoff.projectivePointLogCutoff_support V e x hx) x m ε hε

theorem projectivePointLogPotential_real (ε : ℝ) (hε : 0 < ε) :
    ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm (projectivePointLogPotential V e he x hx m ε hε) = projectivePointLogPotential V e he x hx m ε hε :=
  Projective.LogPointPotential.projectiveLogPointPotential_real V e he _ _ _ _ x m ε hε

theorem projectivePointLogPotential_exp_near (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ z in 𝓝 x, Real.exp (ScalarPotentialFunctions.realPotentialScalar (projectivePointLogPotential V e he x hx m ε hε)
      (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z)) = ((ε + ‖z - x‖ ^ 2) ^ m)⁻¹ := by
  filter_upwards [(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hx,
    PointLogCutoff.projectivePointLogCutoff_one_near V e x hx] with z hz hηz
  have hone : PointLogCutoff.projectivePointLogCutoff V e x hx (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z)) = 1 :=
    (congrArg (PointLogCutoff.projectivePointLogCutoff V e x hx) (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward_inverse V e z hz)).trans hηz
  exact (Projective.LogPointPotential.projectiveLogPointPotential_exp_one V e he _ _ _ _ x m ε hε (e.map_target hz) hone).trans
    (congrArg (fun w : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V => ((ε + ‖w - x‖ ^ 2) ^ m)⁻¹) (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward_inverse V e z hz))

theorem projectivePointLogPotential_native_solvers
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ 1 →
      ((Holomorphic.PositiveCurvature.positiveHolomorphicTwistMetric V u h n).withPotential
        (projectivePointLogPotential V e he x hx m ε hε)).hasBoundedSmoothDolbeaultPrimitives V :=
  Positive.LogPointCoercivity.positiveHolomorphicTwistMetric_log_point_dolbeault V h e he _ _ _ _ x
    (PointLogCutoff.projectivePointLogCutoff_one_near V e x hx) m

end

/-! One genuine coordinate neighborhood carries the exact logarithmic weight for every positive regularization parameter. -/

open Filter _root_.Metric Set
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem projectivePointLogPotential_uniform_neighborhood (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (x : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hx : x ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ∃ R : ℝ, 0 < R ∧ closedBall x R ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e ∧
      ∀ (m : ℕ) (ε : ℝ) (hε : 0 < ε) (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V), z ∈ closedBall x R →
      Real.exp (ScalarPotentialFunctions.realPotentialScalar (projectivePointLogPotential V e he x hx m ε hε)
        (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z)) = ((ε + ‖z - x‖ ^ 2) ^ m)⁻¹ := by
  have hn : {z | z ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e ∧ PointLogCutoff.projectivePointLogCutoff V e x hx z = 1} ∈ 𝓝 x := by
    filter_upwards [(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hx,
      PointLogCutoff.projectivePointLogCutoff_one_near V e x hx] with z hz hη
    exact ⟨hz, hη⟩
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp hn
  have hclosed : closedBall x (r / 2) ⊆
      {z | z ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e ∧ PointLogCutoff.projectivePointLogCutoff V e x hx z = 1} :=
    (closedBall_subset_ball (half_lt_self hr)).trans hb
  refine ⟨r / 2, half_pos hr, fun z hz => (hclosed hz).1, fun m ε hε z hz => ?_⟩
  have hzD := (hclosed hz).1
  have hone : PointLogCutoff.projectivePointLogCutoff V e x hx (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z)) = 1 :=
    (congrArg (PointLogCutoff.projectivePointLogCutoff V e x hx) (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward_inverse V e z hzD)).trans (hclosed hz).2
  exact (Projective.LogPointPotential.projectiveLogPointPotential_exp_one V e he _ _ _ _ x m ε hε (e.map_target hzD) hone).trans
    (congrArg (fun w : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V => ((ε + ‖w - x‖ ^ 2) ^ m)⁻¹)
      (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward_inverse V e z hzD))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.PointLogMetricSolver
