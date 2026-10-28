import OAI.AlgebraicGeometry.Comparison.Betti.Open.ParameterMixedJetApproximation
import OAI.AlgebraicGeometry.Comparison.Betti.Open.ParameterExhaustion
import OAI.AlgebraicGeometry.Comparison.Betti.Open.ExpandingParametricPrimitives
import OAI.AlgebraicGeometry.Comparison.Betti.ParametricCorrectionOrders

/-! # Parametric Cauchy Corrections -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.ParametricCauchyCorrections.Dolbeault

noncomputable section

section

/-! One actual Cauchy truncation order controls all mixed jets on each
compact set of the open parameter exhaustion and its expanding line disc. -/

open _root_.TopologicalSpace Set _root_.Metric
open scoped ContDiff

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℂ P]
  [IsScalarTower ℝ ℂ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

theorem exists_openParametricCorrectionOrder (S : Opens P) {g : P × ℂ → F}
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ)) (n : ℕ) :
    ∃ N : ℕ, ∀ M ≥ N, ∀ k ≤ n, ∀ l ≤ n,
      ∀ z ∈ closedBall 0 (n : ℝ), ∀ p ∈ ParameterExhaustion.Dolbeault.openParameterCompact S n,
      ‖iteratedDeriv l (fun w => OperatorParameterJets.Dolbeault.parameterJet
          (Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyDifference g n) 0 (ParametricCorrectionOrders.Dolbeault.parametricCorrectionRadius n) M)
          k (p, w)) z -
        iteratedDeriv l (fun w => OperatorParameterJets.Dolbeault.parameterJet (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyDifference g n) k (p, w)) z‖ <
        (1 / 2 : ℝ) ^ (n + 1) := by
  have hs : (n : NNReal) < ParametricCorrectionOrders.Dolbeault.parametricCorrectionRadius n := by
    unfold ParametricCorrectionOrders.Dolbeault.parametricCorrectionRadius
    exact lt_add_of_pos_right _ (by norm_num)
  have hsub : closedBall 0 (ParametricCorrectionOrders.Dolbeault.parametricCorrectionRadius n : ℝ) ⊆ ball (0 : ℂ) ((n : ℝ) + 1) := by
    apply closedBall_subset_ball
    simp only [ParametricCorrectionOrders.Dolbeault.parametricCorrectionRadius, NNReal.coe_add, NNReal.coe_natCast,
      NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
    linarith
  have hhol : ∀ p ∈ S, DifferentiableOn ℂ (fun z => ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyDifference g n (p, z))
      (ball 0 ((n : ℝ) + 1)) :=
    fun _ hp => (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyDifference_holomorphic_on hg n hp).mono ball_subset_closedBall
  exact ParameterMixedJetApproximation.Dolbeault.exists_uniform_openParameter_mixedJets_approx S.isOpen (ParameterExhaustion.Dolbeault.openParameterCompact_isCompact S n)
    (ParameterExhaustion.Dolbeault.openParameterCompact_subset S n) (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyDifference_smoothOn S.isOpen hg n)
    isOpen_ball hhol (ParametricCorrectionOrders.Dolbeault.parametricCorrectionRadius_pos n) hs hsub
    (by positivity : 0 < (1 / 2 : ℝ) ^ (n + 1)) n

end

/-! Actual Cauchy correction polynomials over open parameter domains,
chosen using simultaneous mixed derivative bounds on compact exhaustions. -/

open _root_.TopologicalSpace Set _root_.Metric
open scoped ContDiff

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℂ P]
  [IsScalarTower ℝ ℂ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

def openParametricCauchyCorrectionPolynomial (S : Opens P) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ)) (n : ℕ) : P × ℂ → F :=
  Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyDifference g n) 0 (ParametricCorrectionOrders.Dolbeault.parametricCorrectionRadius n)
    (Classical.choose (exists_openParametricCorrectionOrder S hg n))

theorem openParametricCauchyCorrectionPolynomial_smooth (S : Opens P) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ)) (n : ℕ) :
    ContDiffOn ℝ ∞ (openParametricCauchyCorrectionPolynomial S g hg n) ((S : Set P) ×ˢ univ) :=
  Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial_smooth (S.isOpen.prod isOpen_univ)
    (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyDifference_smoothOn S.isOpen hg n) S.isOpen
    (ParametricCorrectionOrders.Dolbeault.parametricCorrectionRadius_pos n) (prod_mono Subset.rfl (subset_univ _)) _

theorem openParametricCauchyCorrectionPolynomial_entire (S : Opens P) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ)) (n : ℕ) (p : P) :
    Differentiable ℂ (fun z => openParametricCauchyCorrectionPolynomial S g hg n (p, z)) := by
  change Differentiable ℂ ((cauchyPowerSeries
    (fun z => ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyDifference g n (p, z)) 0 (ParametricCorrectionOrders.Dolbeault.parametricCorrectionRadius n)).partialSum
      (Classical.choose (exists_openParametricCorrectionOrder S hg n)))
  exact Holomorphic.DiscApproximation.Dolbeault.powerSeriesPartialSum_entire _ _

theorem openParametricCauchyCorrectionPolynomial_mixed_bound (S : Opens P) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ))
    (n k l : ℕ) (hk : k ≤ n) (hl : l ≤ n) {z : ℂ} (hz : z ∈ closedBall 0 (n : ℝ))
    {p : P} (hp : p ∈ ParameterExhaustion.Dolbeault.openParameterCompact S n) :
    ‖iteratedDeriv l (fun w => OperatorParameterJets.Dolbeault.parameterJet (openParametricCauchyCorrectionPolynomial S g hg n) k (p, w)) z -
      iteratedDeriv l (fun w => OperatorParameterJets.Dolbeault.parameterJet (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyDifference g n) k (p, w)) z‖ ≤
      (1 / 2 : ℝ) ^ (n + 1) :=
  (Classical.choose_spec (exists_openParametricCorrectionOrder S hg n) _ le_rfl k hk l hl z hz p hp).le

def correctedOpenParametricCauchyDifference (S : Opens P) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ)) (n : ℕ) : P × ℂ → F :=
  fun q => ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyDifference g n q - openParametricCauchyCorrectionPolynomial S g hg n q

theorem correctedOpenParametricCauchyDifference_smooth (S : Opens P) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ)) (n : ℕ) :
    ContDiffOn ℝ ∞ (correctedOpenParametricCauchyDifference S g hg n) ((S : Set P) ×ˢ univ) :=
  (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyDifference_smoothOn S.isOpen hg n).sub
    (openParametricCauchyCorrectionPolynomial_smooth S g hg n)

theorem correctedOpenParametricCauchyDifference_holomorphic (S : Opens P) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ)) (n : ℕ) {p : P} (hp : p ∈ S) :
    DifferentiableOn ℂ (fun z => correctedOpenParametricCauchyDifference S g hg n (p, z))
      (closedBall 0 ((n : ℝ) + 1)) :=
  (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyDifference_holomorphic_on hg n hp).sub
    (openParametricCauchyCorrectionPolynomial_entire S g hg n p).differentiableOn

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.ParametricCauchyCorrections.Dolbeault
