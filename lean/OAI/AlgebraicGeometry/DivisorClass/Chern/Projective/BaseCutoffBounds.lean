import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.BaseChartCutoffs
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.CutoffEnergy
import OAI.AlgebraicGeometry.DivisorClass.Chern.Positive.BochnerCutoff

/-! # Base Cutoff Bounds -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.BaseCutoffBounds

noncomputable section

/-! The fixed base partition has uniform error bounds and a single eventual twist threshold for all its original chart inequalities. -/

open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

def projectiveBaseCutoffErrorBound (i : BasePartition.projectiveBaseFiniteCover V) : ℝ :=
  (CutoffEnergy.projectiveCutoffEnergy_bound V (chartAt V.analyticModel i.val) (chart_mem_atlas V.analyticModel i.val)
    (BaseChartCutoffs.projectiveBaseChartCutoff V i) (BaseChartCutoffs.projectiveBaseChartCutoff_smooth V i)
    (BaseChartCutoffs.projectiveBaseChartCutoff_compact V i) (BaseChartCutoffs.projectiveBaseChartCutoff_support V i)).choose

theorem projectiveBaseCutoffErrorBound_pos (i : BasePartition.projectiveBaseFiniteCover V) : 0 < projectiveBaseCutoffErrorBound V i :=
  (CutoffEnergy.projectiveCutoffEnergy_bound V (chartAt V.analyticModel i.val) (chart_mem_atlas V.analyticModel i.val)
    (BaseChartCutoffs.projectiveBaseChartCutoff V i) (BaseChartCutoffs.projectiveBaseChartCutoff_smooth V i)
    (BaseChartCutoffs.projectiveBaseChartCutoff_compact V i) (BaseChartCutoffs.projectiveBaseChartCutoff_support V i)).choose_spec.1

theorem projectiveBaseCutoffEnergy_bound (i : BasePartition.projectiveBaseFiniteCover V) (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    CutoffEnergy.projectiveCutoffEnergy V (chartAt V.analyticModel i.val) (BaseChartCutoffs.projectiveBaseChartCutoff V i) z ≤
      projectiveBaseCutoffErrorBound V i :=
  (CutoffEnergy.projectiveCutoffEnergy_bound V (chartAt V.analyticModel i.val) (chart_mem_atlas V.analyticModel i.val)
    (BaseChartCutoffs.projectiveBaseChartCutoff V i) (BaseChartCutoffs.projectiveBaseChartCutoff_smooth V i)
    (BaseChartCutoffs.projectiveBaseChartCutoff_compact V i) (BaseChartCutoffs.projectiveBaseChartCutoff_support V i)).choose_spec.2 z

def projectiveBaseTotalCutoffErrorBound : ℝ := (∑ i, projectiveBaseCutoffErrorBound V i) + 1

theorem projectiveBaseTotalCutoffErrorBound_pos : 0 < projectiveBaseTotalCutoffErrorBound V := by
  have hn : 0 ≤ ∑ i, projectiveBaseCutoffErrorBound V i :=
    Finset.sum_nonneg (fun i _ => (projectiveBaseCutoffErrorBound_pos V i).le)
  unfold projectiveBaseTotalCutoffErrorBound
  linarith

theorem projectiveBaseCutoffEnergy_sum_bound
    (z : BasePartition.projectiveBaseFiniteCover V → ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    (∑ i, CutoffEnergy.projectiveCutoffEnergy V (chartAt V.analyticModel i.val) (BaseChartCutoffs.projectiveBaseChartCutoff V i) (z i)) ≤
      projectiveBaseTotalCutoffErrorBound V := by
  apply (Finset.sum_le_sum (fun i _ => projectiveBaseCutoffEnergy_bound V i (z i))).trans
  unfold projectiveBaseTotalCutoffErrorBound
  linarith

theorem positiveHolomorphicTwistMetric_all_base_cutoffs
    (u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace) (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (c : ℝ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → ∀ i : BasePartition.projectiveBaseFiniteCover V,
      (Holomorphic.PositiveCurvature.positiveHolomorphicTwistMetric V u h n).projectiveBochnerCutoffLowerBound V
        (chartAt V.analyticModel i.val) (BaseChartCutoffs.projectiveBaseChartCutoff V i) c := by
  classical
  have ht (i : BasePartition.projectiveBaseFiniteCover V) := Positive.BochnerCutoff.positiveHolomorphicTwistMetric_bochner_cutoff_bound V u h
    (chartAt V.analyticModel i.val) (chart_mem_atlas V.analyticModel i.val)
    (BaseChartCutoffs.projectiveBaseChartCutoff V i) (BaseChartCutoffs.projectiveBaseChartCutoff_smooth V i)
    (BaseChartCutoffs.projectiveBaseChartCutoff_compact V i) (BaseChartCutoffs.projectiveBaseChartCutoff_support V i) c
  choose N _ hN using ht
  refine ⟨(∑ i, N i) + 1, by omega, ?_⟩
  intro n hn i
  apply hN i n
  exact (Finset.single_le_sum (fun j _ => Nat.zero_le (N j)) (Finset.mem_univ i)).trans
    ((Nat.le_succ _).trans hn)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.BaseCutoffBounds
