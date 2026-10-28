import OAI.Analysis.PDE.Green.LocalExtension

/-! Smooth sublevel localization on an active parameter set.  The extension
is exact on those fibers; outside them it may have a degenerate zero level,
which is harmless for the localized Green theorem. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter
open scoped Topology

theorem exists_active_sublevel_extension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {r : E → ℝ} {k : ℕ∞} (hr : ContDiffOn ℝ k r U)
    (hcover : ∀ x ∈ S, r x ≤ 0 → x ∈ K) :
    ∃ R : E → ℝ, ContDiff ℝ k R ∧
      (∀ x ∈ S, r x ≤ 0 → R =ᶠ[𝓝 x] r) ∧
      (∀ x ∈ S, R x < 0 ↔ r x < 0) ∧
      (∀ x ∈ S, R x ≤ 0 ↔ r x ≤ 0) ∧
      (∀ x, 0 < r x → 0 < R x) := by
  obtain ⟨χ, hχ, hχrange, hχone, hχzero⟩ :=
    exists_smooth_cutoff_near_compact hK hU hKU (k := k)
  let R : E → ℝ := fun x => χ x * (r x - 1) + 1
  have hR : ContDiff ℝ k R :=
    (contDiff_cutoff_smul hU hχ hχzero (hr.sub contDiffOn_const)).add contDiff_const
  have hsame (x : E) (hx : x ∈ S) (hrx : r x ≤ 0) : R =ᶠ[𝓝 x] r := by
    filter_upwards [hχone x (hcover x hx hrx)] with y hy
    dsimp only [R]
    rw [hy]
    ring
  have hpos (x : E) (hx : 0 < r x) : 0 < R x := by
    have hχ0 := (hχrange x).1
    have hχ1 := (hχrange x).2
    dsimp only [R]
    by_cases hc : χ x = 1
    · simpa only [hc, one_mul, sub_add_cancel] using hx
    · have hlt : χ x < 1 := lt_of_le_of_ne hχ1 hc
      have hn := mul_nonneg hχ0 hx.le
      nlinarith
  refine ⟨R, hR, hsame, ?_, ?_, hpos⟩
  · intro x hx
    by_cases hrx : r x ≤ 0
    · rw [(hsame x hx hrx).eq_of_nhds]
    · have hp := hpos x (lt_of_not_ge hrx)
      exact iff_of_false (not_lt.mpr hp.le) (not_lt.mpr (lt_of_not_ge hrx).le)
  · intro x hx
    by_cases hrx : r x ≤ 0
    · rw [(hsame x hx hrx).eq_of_nhds]
    · exact iff_of_false (not_le.mpr (hpos x (lt_of_not_ge hrx))) hrx

end OAI.Analysis.PDE.Green
