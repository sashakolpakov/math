import OAI.Analysis.PDE.Dirichlet.DensityPath
import Mathlib.Analysis.Calculus.ContDiff.RCLike

open Set Filter
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

/-- Uniform spatial Lipschitz control of the logarithm of the entire positive
affine density path on an arbitrary compact set. No convexity of the physical
domain is required: local C¹ control is globalized on parameter times space. -/
theorem densityPath_uniform_log_lipschitz_compact {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : IsCompact S) {F₀ F₁ : E → ℝ}
    (h₀ : ContDiff ℝ 2 F₀) (h₁ : ContDiff ℝ 2 F₁)
    (hpos₀ : ∀ x ∈ S, 0 < F₀ x) (hpos₁ : ∀ x ∈ S, 0 < F₁ x) :
    ∃ L : ℝ, 0 < L ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ S, ∀ y ∈ S,
      |Real.log (densityPath F₀ F₁ t x) - Real.log (densityPath F₀ F₁ t y)| ≤
        L * dist x y := by
  let G : ℝ × E → ℝ := fun p ↦ Real.log (densityPath F₀ F₁ p.1 p.2)
  have hlocal : LocallyLipschitzOn (Icc (0 : ℝ) 1 ×ˢ S) G := by
    intro p hp
    have hg : ContDiffAt ℝ 1 G p :=
      ((contDiff_densityPath_joint h₀ h₁).contDiffAt.log
        (densityPath_pos (hpos₀ p.2 hp.2) (hpos₁ p.2 hp.2) hp.1).ne').of_le (by norm_num)
    obtain ⟨K, U, hU, hKU⟩ := hg.exists_lipschitzOnWith
    exact ⟨K, U, mem_nhdsWithin_of_mem_nhds hU, hKU⟩
  obtain ⟨L, hL⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_Icc.prod hS) hlocal
  refine ⟨(L : ℝ) + 1, by positivity, ?_⟩
  intro t ht x hx y hy
  have hb := hL.dist_le_mul (t, x) ⟨ht, hx⟩ (t, y) ⟨ht, hy⟩
  have hb' : |Real.log (densityPath F₀ F₁ t x) - Real.log (densityPath F₀ F₁ t y)| ≤
      (L : ℝ) * dist x y := by simpa [G, Real.dist_eq, Prod.dist_eq, max_eq_right (dist_nonneg)] using hb
  exact hb'.trans (mul_le_mul_of_nonneg_right (by linarith) dist_nonneg)

end OAI.Analysis.PDE.Dirichlet
