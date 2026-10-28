import OAI.AlgebraicGeometry.Comparison.Betti.UniformFamilyPolynomialApproximation
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.DerivativeApproximation

/-! # Compact Family Derivative Approximation -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.CompactFamilyDerivativeApproximation.Dolbeault

noncomputable section

/-! Cauchy polynomials approximate all complex derivatives uniformly
over a compact parameter family. Evaluation uses the actual derivatives
of the Banach-valued family in its supremum norm. -/

open Set Filter _root_.Metric
open scoped _root_.Topology

variable {K F : Type} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem compactFamily_holomorphic {g : ℂ → C(K, F)} {r : NNReal} (hr : 0 < r)
    (hg : ContinuousOn g (closedBall 0 r))
    (hhol : ∀ p : K, DifferentiableOn ℂ (fun z => g z p) (closedBall 0 r)) :
    DifferentiableOn ℂ g (ball 0 r) := by
  simpa only [Metric.eball_coe] using
    (CompactHolomorphicFamilies.Dolbeault.compactFamily_hasFPowerSeriesOnBall hr hg hhol).analyticOnNhd.differentiableOn

theorem compactFamily_iteratedDeriv_uniform {g : ℂ → C(K, F)} {r s : NNReal}
    (hr : 0 < r) (hs : s < r) (hg : ContinuousOn g (closedBall 0 r))
    (hhol : ∀ p : K, DifferentiableOn ℂ (fun z => g z p) (closedBall 0 r)) (k : ℕ) :
    TendstoUniformlyOn (fun n => iteratedDeriv k (fun z => (cauchyPowerSeries g 0 r).partialSum n z))
      (iteratedDeriv k g) atTop (closedBall 0 (s : ℝ)) := by
  have hconv : TendstoLocallyUniformlyOn (fun n z => (cauchyPowerSeries g 0 r).partialSum n z)
      g atTop (ball 0 (r : ℝ)) := by
    simpa only [zero_add, Metric.eball_coe] using
      (CompactHolomorphicFamilies.Dolbeault.compactFamily_hasFPowerSeriesOnBall hr hg hhol).tendstoLocallyUniformlyOn
  exact (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).mp
    (Holomorphic.DerivativeApproximation.Dolbeault.holomorphicLocallyUniform_iteratedDeriv hconv
      (fun n => (Holomorphic.DiscApproximation.Dolbeault.powerSeriesPartialSum_entire (cauchyPowerSeries g 0 r) n).differentiableOn)
      isOpen_ball k) (closedBall 0 s) (closedBall_subset_ball hs) (isCompact_closedBall 0 s)

theorem exists_uniform_compactFamily_derivative_approx {g : ℂ → C(K, F)} {r s : NNReal}
    (hr : 0 < r) (hs : s < r) (hg : ContinuousOn g (closedBall 0 r))
    (hhol : ∀ p : K, DifferentiableOn ℂ (fun z => g z p) (closedBall 0 r))
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ z ∈ closedBall 0 (s : ℝ), ∀ p : K,
      ‖iteratedDeriv k (Holomorphic.DiscApproximation.Dolbeault.holomorphicDiscPartialSum (fun w => g w p) r n) z -
        iteratedDeriv k (fun w => g w p) z‖ < ε := by
  have hconv := Metric.tendstoUniformlyOn_iff.mp
    (compactFamily_iteratedDeriv_uniform hr hs hg hhol k) ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp hconv
  refine ⟨N, ?_⟩
  intro n hn z hz p
  have hzb : z ∈ ball 0 (r : ℝ) := closedBall_subset_ball hs hz
  have heP : (fun w => (ContinuousMap.evalCLM ℂ p) ((cauchyPowerSeries g 0 r).partialSum n w)) =
      Holomorphic.DiscApproximation.Dolbeault.holomorphicDiscPartialSum (fun w => g w p) r n :=
    funext (fun w => UniformFamilyPolynomialApproximation.Dolbeault.compactFamily_partialSum_apply hr hg n w p)
  have he1 := Holomorphic.DerivativeApproximation.Dolbeault.holomorphic_iteratedDeriv_map (ContinuousMap.evalCLM ℂ p) isOpen_univ
    (Holomorphic.DiscApproximation.Dolbeault.powerSeriesPartialSum_entire (cauchyPowerSeries g 0 r) n).differentiableOn k (mem_univ z)
  rw [heP] at he1
  have he2 := Holomorphic.DerivativeApproximation.Dolbeault.holomorphic_iteratedDeriv_map (ContinuousMap.evalCLM ℂ p) isOpen_ball
    (compactFamily_holomorphic hr hg hhol) k hzb
  erw [he1, he2]
  have hb := hN n hn z hz
  rw [dist_eq_norm, norm_sub_rev] at hb
  exact (ContinuousMap.norm_coe_le_norm
    (iteratedDeriv k (fun w => (cauchyPowerSeries g 0 r).partialSum n w) z - iteratedDeriv k g z) p).trans_lt hb

end

end OAI.AlgebraicGeometry.Comparison.Betti.CompactFamilyDerivativeApproximation.Dolbeault
