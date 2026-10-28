import OAI.AlgebraicGeometry.Comparison.Betti.Open.CorrectedParametricJetBounds
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! # Parametric Series Convergence -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.ParametricSeriesConvergence.Dolbeault

noncomputable section

/-! Pointwise and compact uniform convergence of the actual corrected
families and their mixed derivative arrays over an open parameter domain. -/

open _root_.TopologicalSpace Set _root_.Metric Filter
open scoped ContDiff

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℂ P]
  [IsScalarTower ℝ ℂ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

theorem correctedOpenParametricMixedJets_summable (S : Opens P) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ)) (k l : ℕ) {q : P × ℂ} (hq : q.1 ∈ S) :
    Summable (fun n => MixedJetAlgebra.Dolbeault.mixedParameterJet (ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg n) k l q) := by
  apply Summable.of_norm_bounded_eventually
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1))
  obtain ⟨m, hp, hz⟩ := ParameterExhaustion.Dolbeault.exists_openParameterCompact_product_neighborhood (q := q) S hq
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop m, eventually_ge_atTop k, eventually_ge_atTop l] with n hn hk hl
  have hp' := ParameterExhaustion.Dolbeault.openParameterCompact_mono S hn (interior_subset hp)
  have hz' : q.2 ∈ closedBall 0 (n : ℝ) :=
    closedBall_subset_closedBall (by exact_mod_cast hn) (ball_subset_closedBall hz)
  refine (CorrectedParametricJetBounds.Dolbeault.correctedOpenParametricCauchyDifference_mixed_bound S g hg n k l hk hl hz' hp').trans ?_
  rw [pow_succ]
  exact mul_le_of_le_one_right (by positivity) (by norm_num)

theorem correctedOpenParametricCauchyDifference_summable (S : Opens P) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ)) {q : P × ℂ} (hq : q.1 ∈ S) :
    Summable (fun n => ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg n q) := by
  have h := (continuousMultilinearCurryFin0 ℝ P F).toContinuousLinearEquiv.summable.mpr
    (correctedOpenParametricMixedJets_summable S g hg 0 0 hq)
  exact h

def openParametricCauchyCandidate (S : Opens P) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ)) (q : P × ℂ) : F :=
  ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyPrimitive g 0 q + ∑' n, ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg n q

theorem correctedOpenParametricMixedJets_tail_uniform (S : Opens P) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ)) (k l m r : ℕ) :
    TendstoUniformlyOn
      (fun N q => ∑ n ∈ Finset.range N,
        MixedJetAlgebra.Dolbeault.mixedParameterJet (ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg (n + m)) k l q)
      (fun q => ∑' n, MixedJetAlgebra.Dolbeault.mixedParameterJet (ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg (n + m)) k l q)
      atTop (ParameterExhaustion.Dolbeault.openParameterCompact S r ×ˢ closedBall (0 : ℂ) (r : ℝ)) := by
  apply tendstoUniformlyOn_tsum_nat_eventually
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1))
  filter_upwards [eventually_ge_atTop r, eventually_ge_atTop k, eventually_ge_atTop l] with n hn hk hl
  intro q hq
  have hrn : r ≤ n + m := by omega
  have hb := CorrectedParametricJetBounds.Dolbeault.correctedOpenParametricCauchyDifference_mixed_bound S g hg (n + m) k l
    (by omega) (by omega)
    (closedBall_subset_closedBall (by exact_mod_cast hrn) hq.2) (ParameterExhaustion.Dolbeault.openParameterCompact_mono S hrn hq.1)
  refine hb.trans ?_
  rw [show n + m + 1 = n + (m + 1) by omega, pow_add]
  exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))

theorem correctedOpenParametricMixedJets_tail_continuous (S : Opens P) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ)) (k l m : ℕ) :
    ContinuousOn
      (fun q => ∑' n, MixedJetAlgebra.Dolbeault.mixedParameterJet (ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg (n + m)) k l q)
      (interior (ParameterExhaustion.Dolbeault.openParameterCompact S m) ×ˢ ball (0 : ℂ) (m : ℝ)) := by
  have hconv := (correctedOpenParametricMixedJets_tail_uniform S g hg k l m m).mono
    (prod_mono interior_subset ball_subset_closedBall)
  apply hconv.continuousOn
  apply Frequently.of_forall
  intro N
  apply continuousOn_finsetSum
  intro n hn
  have hhol : ∀ p ∈ S, DifferentiableOn ℂ
      (fun z => ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg (n + m) (p, z)) (ball 0 (m : ℝ)) := by
    intro p hp
    exact (ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference_holomorphic S g hg (n + m) hp).mono
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by push_cast; linarith)))
  exact (MixedJetDifferential.Dolbeault.mixedParameterJet_smoothOn S.isOpen (ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference_smooth S g hg (n + m))
    isOpen_ball hhol k l).continuousOn.mono
      (prod_mono (interior_subset.trans (ParameterExhaustion.Dolbeault.openParameterCompact_subset S m)) Subset.rfl)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.ParametricSeriesConvergence.Dolbeault
