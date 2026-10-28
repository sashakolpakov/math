import OAI.AlgebraicGeometry.Comparison.Betti.OperatorMixedJetApproximation
import OAI.AlgebraicGeometry.Comparison.Betti.ExpandingParametricPrimitives

/-! # Parametric Correction Orders -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ParametricCorrectionOrders.Dolbeault

noncomputable section

/-! One Cauchy truncation order simultaneously controls all mixed
derivative arrays through a prescribed order on expanding compact sets. -/

open Set _root_.Metric
open scoped ContDiff

def parametricCorrectionRadius (n : ℕ) : NNReal := (n : NNReal) + 1 / 2

theorem parametricCorrectionRadius_pos (n : ℕ) : 0 < parametricCorrectionRadius n := by
  unfold parametricCorrectionRadius
  positivity

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℂ P]
  [IsScalarTower ℝ ℂ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

theorem exists_parametricCorrectionOrder {g : P × ℂ → F} (hg : ContDiff ℝ ∞ g) (n : ℕ) :
    ∃ N : ℕ, ∀ M ≥ N, ∀ k ≤ n, ∀ l ≤ n,
      ∀ z ∈ closedBall 0 (n : ℝ), ∀ p ∈ closedBall (0 : P) (n : ℝ),
      ‖iteratedDeriv l (fun w => OperatorParameterJets.Dolbeault.parameterJet
          (Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyDifference g n) 0 (parametricCorrectionRadius n) M)
          k (p, w)) z -
        iteratedDeriv l (fun w => OperatorParameterJets.Dolbeault.parameterJet (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyDifference g n) k (p, w)) z‖ <
        (1 / 2 : ℝ) ^ (n + 1) := by
  let : ProperSpace P := FiniteDimensional.proper ℝ P
  let K := closedBall (0 : P) (n : ℝ)
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall 0 (n : ℝ))
  have hs : (n : NNReal) < parametricCorrectionRadius n := by
    unfold parametricCorrectionRadius
    exact lt_add_of_pos_right _ (by norm_num)
  have hsub : closedBall 0 (parametricCorrectionRadius n : ℝ) ⊆ ball (0 : ℂ) ((n : ℝ) + 1) := by
    apply closedBall_subset_ball
    simp only [parametricCorrectionRadius, NNReal.coe_add, NNReal.coe_natCast,
      NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
    linarith
  have hhol : ∀ p : P, DifferentiableOn ℂ (fun z => ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyDifference g n (p, z))
      (ball 0 ((n : ℝ) + 1)) :=
    fun p => (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyDifference_holomorphic hg n p).mono ball_subset_closedBall
  obtain ⟨N, hN⟩ := OperatorMixedJetApproximation.Dolbeault.exists_uniform_finite_operator_mixedJets_approx
    (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyDifference_smooth hg n) isOpen_ball hhol
    (a := fun p : K => (p : P)) continuous_subtype_val
    (parametricCorrectionRadius_pos n) hs hsub (by positivity : 0 < (1 / 2 : ℝ) ^ (n + 1)) n
  exact ⟨N, fun M hM k hk l hl z hz p hp => hN M hM k hk l hl z hz ⟨p, hp⟩⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.ParametricCorrectionOrders.Dolbeault
