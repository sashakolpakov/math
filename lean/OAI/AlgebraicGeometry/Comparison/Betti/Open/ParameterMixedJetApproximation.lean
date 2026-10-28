import OAI.AlgebraicGeometry.Comparison.Betti.Open.ParameterCutoff
import OAI.AlgebraicGeometry.Comparison.Betti.ParameterFamilyGermCongruence
import OAI.AlgebraicGeometry.Comparison.Betti.OperatorMixedJetApproximation

/-! # Parameter Mixed Jet Approximation -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.ParameterMixedJetApproximation.Dolbeault

noncomputable section

/-! Uniform approximation of actual mixed derivative arrays over compact
sets inside an arbitrary open parameter domain. -/

open Set _root_.Metric Filter
open scoped ContDiff _root_.Topology

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℂ P]
  [IsScalarTower ℝ ℂ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

theorem exists_uniform_openParameter_mixedJets_approx {S K : Set P}
    (hS : IsOpen S) (hK : IsCompact K) (hKS : K ⊆ S)
    {g : P × ℂ → F} (hg : ContDiffOn ℝ ∞ g (S ×ˢ univ))
    {U : Set ℂ} (hU : IsOpen U)
    (hhol : ∀ p ∈ S, DifferentiableOn ℂ (fun z => g (p, z)) U)
    {r s : NNReal} (hr : 0 < r) (hs : s < r) (hsub : closedBall 0 (r : ℝ) ⊆ U)
    {ε : ℝ} (hε : 0 < ε) (m : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ k ≤ m, ∀ l ≤ m,
      ∀ z ∈ closedBall 0 (s : ℝ), ∀ p ∈ K,
      ‖iteratedDeriv l (fun w => OperatorParameterJets.Dolbeault.parameterJet (Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial g 0 r n) k (p, w)) z -
        iteratedDeriv l (fun w => OperatorParameterJets.Dolbeault.parameterJet g k (p, w)) z‖ < ε := by
  obtain ⟨G, hG, hGhol, he⟩ := ParameterCutoff.Dolbeault.exists_global_smooth_family_extension hS hK.isClosed hKS hg hhol
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨N, hN⟩ := OperatorMixedJetApproximation.Dolbeault.exists_uniform_finite_operator_mixedJets_approx hG hU hGhol
    (a := fun p : K => (p : P)) continuous_subtype_val hr hs hsub hε m
  refine ⟨N, ?_⟩
  intro n hn k hk l hl z hz p hp
  have hphe : ∀ᶠ t in 𝓝 p, ∀ w, G (t, w) = g (t, w) :=
    he.filter_mono (nhds_le_nhdsSet hp)
  have hbound := hN n hn k hk l hl z hz ⟨p, hp⟩
  rw [ParameterFamilyGermCongruence.Dolbeault.cauchyPolynomial_mixedJet_eq_of_family_germ hphe,
    ParameterFamilyGermCongruence.Dolbeault.mixedParameterJet_eq_of_family_germ hphe] at hbound
  exact hbound

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.ParameterMixedJetApproximation.Dolbeault
