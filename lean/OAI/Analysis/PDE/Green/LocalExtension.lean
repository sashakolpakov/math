import Mathlib

/-! Smooth localization near a compact sublevel, without altering the domain. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter
open scoped Topology Manifold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_smooth_cutoff_near_compact {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) {k : ℕ∞} :
    ∃ χ : E → ℝ, ContDiff ℝ k χ ∧ (∀ x, χ x ∈ Icc 0 1) ∧
      (∀ x ∈ K, χ =ᶠ[𝓝 x] (fun _ => 1)) ∧
      (∀ x ∉ U, χ =ᶠ[𝓝 x] (fun _ => 0)) := by
  have hd : Disjoint Uᶜ K := disjoint_left.mpr (fun x hx hk => hx (hKU hk))
  obtain ⟨f, hf0, hf1, hf⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (𝓘(ℝ, E)) hU.isClosed_compl hK.isClosed hd (n := k)
  refine ⟨f, ?_, hf, ?_, ?_⟩
  · exact contMDiff_iff_contDiff.mp f.contMDiff
  · intro x hx
    exact hf1.filter_mono (nhds_le_nhdsSet hx)
  · intro x hx
    exact hf0.filter_mono (nhds_le_nhdsSet hx)

omit [FiniteDimensional ℝ E] in
theorem contDiff_cutoff_smul {U : Set E} (hU : IsOpen U) {k : ℕ∞}
    {χ : E → ℝ} (hχ : ContDiff ℝ k χ)
    (hzero : ∀ x ∉ U, χ =ᶠ[𝓝 x] (fun _ => 0))
    {f : E → F} (hf : ContDiffOn ℝ k f U) :
    ContDiff ℝ k (fun x => χ x • f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact hχ.contDiffAt.smul ((hf x hx).contDiffAt (hU.mem_nhds hx))
  · apply (contDiffAt_const : ContDiffAt ℝ k (fun _ : E => (0 : F)) x).congr_of_eventuallyEq
    filter_upwards [hzero x hx] with y hy
    simp only [hy, zero_smul]

/-- Extending a defining function by a positive constant introduces no new
sublevel points and preserves every derivative near the original sublevel. -/
theorem exists_global_sublevel_extension {U : Set E} (hU : IsOpen U)
    {r : E → ℝ} {k : ℕ∞} (hr : ContDiffOn ℝ k r U)
    {δ : ℝ} (hδ : 0 ≤ δ) (hK : IsCompact {x | r x ≤ δ})
    (hKU : {x | r x ≤ δ} ⊆ U) :
    ∃ R : E → ℝ, ContDiff ℝ k R ∧
      (∀ x, r x ≤ 0 → R =ᶠ[𝓝 x] r) ∧
      (∀ x, R x < 0 ↔ r x < 0) ∧ (∀ x, R x ≤ 0 ↔ r x ≤ 0) := by
  obtain ⟨χ, hχ, hχrange, hχone, hχzero⟩ := exists_smooth_cutoff_near_compact hK hU hKU (k := k)
  let R : E → ℝ := fun x => χ x * (r x - 1) + 1
  have hR : ContDiff ℝ k R := by
    exact (contDiff_cutoff_smul hU hχ hχzero (hr.sub contDiffOn_const)).add contDiff_const
  have hsame (x : E) (hx : r x ≤ 0) : R =ᶠ[𝓝 x] r := by
    filter_upwards [hχone x (hx.trans hδ)] with y hy
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
  refine ⟨R, hR, hsame, ?_, ?_⟩
  · intro x
    by_cases hx : r x ≤ 0
    · rw [(hsame x hx).eq_of_nhds]
    · have hp := hpos x (lt_of_not_ge hx)
      exact iff_of_false (not_lt.mpr hp.le) (not_lt.mpr (lt_of_not_ge hx).le)
  · intro x
    by_cases hx : r x ≤ 0
    · rw [(hsame x hx).eq_of_nhds]
    · exact iff_of_false (not_le.mpr (hpos x (lt_of_not_ge hx))) hx

end OAI.Analysis.PDE.Green
