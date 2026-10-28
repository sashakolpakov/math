import OAI.AlgebraicGeometry.Comparison.Betti.CompactHolomorphicFamilies
import OAI.AlgebraicGeometry.Comparison.Betti.CauchyPolynomialNaturality

/-! # Uniform Family Polynomial Approximation -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.UniformFamilyPolynomialApproximation.Dolbeault

noncomputable section

/-! One actual Cauchy-polynomial degree uniformly approximates every
member of a compact holomorphic family on a smaller closed disc. -/

open Filter _root_.Metric
open scoped _root_.Topology

variable {K F : Type} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem compactFamily_partialSum_apply {g : ℂ → C(K, F)} {r : NNReal}
    (hr : 0 < r) (hg : ContinuousOn g (closedBall 0 r)) (n : ℕ) (z : ℂ) (p : K) :
    (cauchyPowerSeries g 0 r).partialSum n z p =
      Holomorphic.DiscApproximation.Dolbeault.holomorphicDiscPartialSum (fun w => g w p) r n z :=
  CauchyPolynomialNaturality.Dolbeault.cauchyPowerSeries_partialSum_map (ContinuousMap.evalCLM ℂ p) hr
    (hg.mono sphere_subset_closedBall) n z

theorem exists_uniform_compactFamily_polynomial_approx {g : ℂ → C(K, F)} {r s : NNReal}
    (hr : 0 < r) (hs : s < r) (hg : ContinuousOn g (closedBall 0 r))
    (hhol : ∀ p : K, DifferentiableOn ℂ (fun z => g z p) (closedBall 0 r))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ z ∈ closedBall 0 (s : ℝ), ∀ p : K,
      ‖Holomorphic.DiscApproximation.Dolbeault.holomorphicDiscPartialSum (fun w => g w p) r n z - g z p‖ < ε := by
  obtain ⟨t, hst, htr⟩ := exists_between hs
  have hu := (CompactHolomorphicFamilies.Dolbeault.compactFamily_tendstoUniformly htr hr hg hhol).mono
    (closedBall_subset_ball (show (s : ℝ) < t from hst))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (Metric.tendstoUniformlyOn_iff.mp hu ε hε)
  refine ⟨N, ?_⟩
  intro n hn z hz p
  have h := hN n hn z hz
  rw [dist_eq_norm, norm_sub_rev] at h
  rw [← compactFamily_partialSum_apply hr hg n z p]
  exact ((ContinuousMap.norm_coe_le_norm
    ((cauchyPowerSeries g 0 r).partialSum n z - g z) p)).trans_lt h

def compactParameterFamily (g : K × ℂ → F) (hg : Continuous g) : ℂ → C(K, F) :=
  fun z => ⟨fun p => g (p, z), hg.comp (continuous_id.prodMk continuous_const)⟩

omit [CompactSpace K] [NormedSpace ℂ F] [CompleteSpace F] in
theorem compactParameterFamily_continuous (g : K × ℂ → F) (hg : Continuous g) :
    Continuous (compactParameterFamily g hg) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact hg.comp continuous_swap

theorem exists_uniform_parameter_polynomial_approx {g : K × ℂ → F} (hg : Continuous g)
    {r s : NNReal} (hr : 0 < r) (hs : s < r)
    (hhol : ∀ p : K, DifferentiableOn ℂ (fun z => g (p, z)) (closedBall 0 r))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ z ∈ closedBall 0 (s : ℝ), ∀ p : K,
      ‖Holomorphic.DiscApproximation.Dolbeault.holomorphicDiscPartialSum (fun w => g (p, w)) r n z - g (p, z)‖ < ε :=
  exists_uniform_compactFamily_polynomial_approx hr hs
    (compactParameterFamily_continuous g hg).continuousOn hhol hε

end

end OAI.AlgebraicGeometry.Comparison.Betti.UniformFamilyPolynomialApproximation.Dolbeault
