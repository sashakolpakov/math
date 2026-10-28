import OAI.AlgebraicGeometry.Comparison.Betti.OperatorParameterJets
import OAI.AlgebraicGeometry.Comparison.Betti.CompactFamilyDerivativeApproximation

/-! # Operator Mixed Jet Approximation -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.OperatorMixedJetApproximation.Dolbeault

noncomputable section

/-! Uniform approximation of mixed derivatives in the operator norm
of the actual multilinear parameter derivative array. -/

open Set _root_.Metric Filter
open scoped ContDiff

variable {P F K : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℂ P]
  [IsScalarTower ℝ ℂ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]
  [TopologicalSpace K] [CompactSpace K]

theorem exists_uniform_operator_mixedJet_approx {g : P × ℂ → F}
    (hg : ContDiff ℝ ∞ g) {U : Set ℂ} (hU : IsOpen U)
    (hhol : ∀ p : P, DifferentiableOn ℂ (fun z => g (p, z)) U)
    (k l : ℕ) {a : K → P} (ha : Continuous a)
    {r s : NNReal} (hr : 0 < r) (hs : s < r) (hsub : closedBall 0 (r : ℝ) ⊆ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ z ∈ closedBall 0 (s : ℝ), ∀ t : K,
      ‖iteratedDeriv l (fun w => OperatorParameterJets.Dolbeault.parameterJet (Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial g 0 r n) k (a t, w)) z -
        iteratedDeriv l (fun w => OperatorParameterJets.Dolbeault.parameterJet g k (a t, w)) z‖ < ε := by
  let G : K × ℂ → ContinuousMultilinearMap ℝ (fun _ : Fin k => P) F :=
    fun q => OperatorParameterJets.Dolbeault.parameterJet g k (a q.1, q.2)
  have hG : Continuous G := (OperatorParameterJets.Dolbeault.parameterJet_contDiff hg k).continuous.comp
    ((ha.comp continuous_fst).prodMk continuous_snd)
  have hGhol : ∀ t : K, DifferentiableOn ℂ (fun w => G (t, w)) (closedBall 0 (r : ℝ)) :=
    fun t => (OperatorParameterJets.Dolbeault.parameterJet_holomorphic hg hU hhol k (a t)).mono hsub
  obtain ⟨N, hN⟩ := CompactFamilyDerivativeApproximation.Dolbeault.exists_uniform_compactFamily_derivative_approx hr hs
    (UniformFamilyPolynomialApproximation.Dolbeault.compactParameterFamily_continuous G hG).continuousOn hGhol l hε
  refine ⟨N, ?_⟩
  intro n hn z hz t
  have he : (fun w => OperatorParameterJets.Dolbeault.parameterJet (Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial g 0 r n) k (a t, w)) =
      Holomorphic.DiscApproximation.Dolbeault.holomorphicDiscPartialSum (fun w => G (t, w)) r n := by
    funext w
    exact OperatorParameterJets.Dolbeault.parameterJet_cauchyPolynomial hg 0 hr n k (a t, w)
  rw [he]
  exact hN n hn z hz t

theorem exists_uniform_finite_operator_mixedJets_approx {g : P × ℂ → F}
    (hg : ContDiff ℝ ∞ g) {U : Set ℂ} (hU : IsOpen U)
    (hhol : ∀ p : P, DifferentiableOn ℂ (fun z => g (p, z)) U)
    {a : K → P} (ha : Continuous a) {r s : NNReal} (hr : 0 < r) (hs : s < r)
    (hsub : closedBall 0 (r : ℝ) ⊆ U) {ε : ℝ} (hε : 0 < ε) (m : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ k ≤ m, ∀ l ≤ m, ∀ z ∈ closedBall 0 (s : ℝ), ∀ t : K,
      ‖iteratedDeriv l (fun w => OperatorParameterJets.Dolbeault.parameterJet (Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial g 0 r n) k (a t, w)) z -
        iteratedDeriv l (fun w => OperatorParameterJets.Dolbeault.parameterJet g k (a t, w)) z‖ < ε := by
  have hEach (k l : ℕ) : ∀ᶠ n in atTop, ∀ z ∈ closedBall 0 (s : ℝ), ∀ t : K,
      ‖iteratedDeriv l (fun w => OperatorParameterJets.Dolbeault.parameterJet (Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial g 0 r n) k (a t, w)) z -
        iteratedDeriv l (fun w => OperatorParameterJets.Dolbeault.parameterJet g k (a t, w)) z‖ < ε :=
    eventually_atTop.mpr (exists_uniform_operator_mixedJet_approx hg hU hhol k l ha hr hs hsub hε)
  have hAll : ∀ᶠ n in atTop, ∀ k ∈ Finset.range (m + 1), ∀ l ∈ Finset.range (m + 1),
      ∀ z ∈ closedBall 0 (s : ℝ), ∀ t : K,
      ‖iteratedDeriv l (fun w => OperatorParameterJets.Dolbeault.parameterJet (Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial g 0 r n) k (a t, w)) z -
        iteratedDeriv l (fun w => OperatorParameterJets.Dolbeault.parameterJet g k (a t, w)) z‖ < ε := by
    rw [eventually_all_finset]
    intro k hk
    rw [eventually_all_finset]
    intro l hl
    exact hEach k l
  obtain ⟨N, hN⟩ := eventually_atTop.mp hAll
  refine ⟨N, fun n hn k hk l hl z hz t => ?_⟩
  exact hN n hn k (Finset.mem_range.mpr (by omega)) l (Finset.mem_range.mpr (by omega)) z hz t

end

end OAI.AlgebraicGeometry.Comparison.Betti.OperatorMixedJetApproximation.Dolbeault
