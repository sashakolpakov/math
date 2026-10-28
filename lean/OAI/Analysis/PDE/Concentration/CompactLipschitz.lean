import OAI.Analysis.PDE.Concentration.GaussianFamily

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Metric
open scoped ContDiff

/-- A smooth map near a compact set has one uniform Lipschitz constant for
all sufficiently short displacements from that set, without assuming its
domain or the compact set is convex. -/
theorem compact_uniform_local_lipschitz
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {f : E → F} (hf : ContDiffOn ℝ ∞ f U) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ x ∈ K, ∀ y, ‖y - x‖ ≤ δ →
      y ∈ U ∧ ‖f y - f x‖ ≤ C * ‖y - x‖ := by
  obtain ⟨δ, hδ, hth⟩ := hK.exists_cthickening_subset_open hU hKU
  have hcompact : IsCompact (cthickening δ K) := hK.cthickening
  obtain ⟨g, hg, heq⟩ := exists_global_smooth_extension_near_compact hcompact hU hth hf
  obtain ⟨R, hR⟩ := hcompact.isBounded.subset_closedBall (0 : E)
  obtain ⟨C, hC⟩ := hg.contDiffOn.exists_lipschitzOnWith (by simp : (∞ : ℕ∞ω) ≠ 0)
    (convex_closedBall (0 : E) R) (isCompact_closedBall (0 : E) R)
  refine ⟨δ, (C : ℝ) + 1, hδ, by positivity, ?_⟩
  intro x hx y hy
  have hxx : x ∈ cthickening δ K :=
    closedBall_subset_cthickening hx δ (mem_closedBall_self hδ.le)
  have hyx : y ∈ cthickening δ K := closedBall_subset_cthickening hx δ
    (by simpa only [mem_closedBall, dist_eq_norm] using hy)
  refine ⟨hth hyx, ?_⟩
  have he := hC.norm_sub_le (hR hyx) (hR hxx)
  rw [(heq y hyx).self_of_nhds, (heq x hxx).self_of_nhds] at he
  exact he.trans (by nlinarith [norm_nonneg (y - x)])

end OAI.Analysis.PDE.Concentration
