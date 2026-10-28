import OAI.AlgebraicGeometry.Comparison.Betti.Open.ParametricCauchyCorrections
import OAI.AlgebraicGeometry.Comparison.Betti.Open.MixedJetDifferential

/-! # Corrected Parametric Jet Bounds -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.CorrectedParametricJetBounds.Dolbeault

noncomputable section

/-! Geometric bounds for all actual mixed jets of the corrected
families on compact subsets of the open parameter domain. -/

open _root_.TopologicalSpace Set _root_.Metric
open scoped ContDiff

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℂ P]
  [IsScalarTower ℝ ℂ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

theorem correctedOpenParametricCauchyDifference_mixed_bound (S : Opens P) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ))
    (n k l : ℕ) (hk : k ≤ n) (hl : l ≤ n) {z : ℂ} (hz : z ∈ closedBall 0 (n : ℝ))
    {p : P} (hp : p ∈ ParameterExhaustion.Dolbeault.openParameterCompact S n) :
    ‖MixedJetAlgebra.Dolbeault.mixedParameterJet (ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg n) k l (p, z)‖ ≤
      (1 / 2 : ℝ) ^ (n + 1) := by
  have hzg : z ∈ ball (0 : ℂ) ((n : ℝ) + 1) := closedBall_subset_ball (by linarith) hz
  have hdiff : ∀ p ∈ S, DifferentiableOn ℂ (fun w => ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyDifference g n (p, w))
      (ball 0 ((n : ℝ) + 1)) :=
    fun _ hpS => (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyDifference_holomorphic_on hg n hpS).mono ball_subset_closedBall
  change ‖MixedJetAlgebra.Dolbeault.mixedParameterJet (fun q => ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyDifference g n q -
    ParametricCauchyCorrections.Dolbeault.openParametricCauchyCorrectionPolynomial S g hg n q) k l (p, z)‖ ≤ _
  rw [MixedJetDifferential.Dolbeault.mixedParameterJet_sub_on S.isOpen (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyDifference_smoothOn S.isOpen hg n)
    (ParametricCauchyCorrections.Dolbeault.openParametricCauchyCorrectionPolynomial_smooth S g hg n) isOpen_ball hdiff
    (fun p _ => (ParametricCauchyCorrections.Dolbeault.openParametricCauchyCorrectionPolynomial_entire S g hg n p).differentiableOn)
    k l ⟨ParameterExhaustion.Dolbeault.openParameterCompact_subset S n hp, hzg⟩]
  exact (norm_sub_rev _ _).le.trans
    (ParametricCauchyCorrections.Dolbeault.openParametricCauchyCorrectionPolynomial_mixed_bound S g hg n k l hk hl hz hp)

theorem correctedOpenParametricCauchyDifference_bound (S : Opens P) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ)) (n : ℕ) {q : P × ℂ}
    (hp : q.1 ∈ ParameterExhaustion.Dolbeault.openParameterCompact S n) (hz : q.2 ∈ closedBall 0 (n : ℝ)) :
    ‖ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg n q‖ ≤ (1 / 2 : ℝ) ^ (n + 1) := by
  have h := correctedOpenParametricCauchyDifference_mixed_bound S g hg n 0 0
    (Nat.zero_le n) (Nat.zero_le n) hz hp
  rwa [MixedJetAlgebra.Dolbeault.norm_mixedParameterJet_zero] at h

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.CorrectedParametricJetBounds.Dolbeault
