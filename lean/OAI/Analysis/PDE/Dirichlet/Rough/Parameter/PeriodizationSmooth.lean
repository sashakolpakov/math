import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.Periodization

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

namespace ParameterDeformation

open OAI.Analysis.Calculus.SmoothExtension

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
variable {E T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [AddCommGroup T]

omit [NormedSpace ℝ E] in
theorem locallyFinite_compact_translates (L : T →+ E)
    (hL : ∀ R : ℝ, {z : T | ‖L z‖ ≤ R}.Finite)
    {K : Set E} (hK : IsCompact K) :
    LocallyFinite (fun z : T ↦ {x | x + L z ∈ K}) := by
  obtain ⟨R, hR, hb⟩ := hK.isBounded.exists_pos_norm_le
  intro x
  refine ⟨ball x 1, ball_mem_nhds x (by norm_num), ?_⟩
  apply (hL (R + (‖x‖ + 1))).subset
  rintro z ⟨y, hy, hyx⟩
  have hn := hb (y + L z) hy
  have hd : ‖y - x‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hyx
  have hny : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by simpa using norm_add_le (y - x) x
  have hz : ‖L z‖ ≤ ‖y + L z‖ + ‖y‖ := by simpa using norm_sub_le (y + L z) y
  change ‖L z‖ ≤ R + (‖x‖ + 1)
  linarith

theorem contDiffAt_parametricPeriodization
    (L : T →+ E) (hL : ∀ R : ℝ, {z : T | ‖L z‖ ≤ R}.Finite)
    {K : Set E} (hK : IsCompact K) (h : Z × E → E)
    (hs : ∀ t x, x ∉ K → h (t, x) = 0)
    (p : Z × E) {q : ℕ∞ω} (hh : ∀ z, ContDiffAt ℝ q h (p.1, p.2 + L z)) :
    ContDiffAt ℝ q (fun a : Z × E ↦ OAI.Analysis.Calculus.SmoothExtension.vectorPeriodization L (fun x ↦ h (a.1, x)) a.2) p := by
  classical
  obtain ⟨U, hU, hfin⟩ := ParameterDeformation.locallyFinite_compact_translates L hL hK p.2
  have heq : (fun a : Z × E ↦ OAI.Analysis.Calculus.SmoothExtension.vectorPeriodization L (fun x ↦ h (a.1, x)) a.2) =ᶠ[𝓝 p]
      (fun a ↦ ∑ z ∈ hfin.toFinset, h (a.1, a.2 + L z)) := by
    filter_upwards [(continuous_snd.tendsto p).eventually hU] with a ha
    apply tsum_eq_sum
    intro z hz
    apply hs
    intro hmem
    exact hz (hfin.mem_toFinset.mpr ⟨a.2, hmem, ha⟩)
  have hf : ContDiffAt ℝ q (fun a : Z × E ↦ ∑ z ∈ hfin.toFinset, h (a.1, a.2 + L z)) p := by
    apply ContDiffAt.sum
    intro z hz
    exact (hh z).comp p (contDiffAt_fst.prodMk (contDiffAt_snd.add contDiffAt_const))
  exact hf.congr_of_eventuallyEq heq

theorem contDiffOn_parametricPeriodization
    (L : T →+ E) (hL : ∀ R : ℝ, {z : T | ‖L z‖ ≤ R}.Finite)
    {K : Set E} (hK : IsCompact K) (h : Z × E → E)
    (hs : ∀ t x, x ∉ K → h (t, x) = 0)
    {I : Set Z} (hI : IsOpen I) {q : ℕ∞ω}
    (hh : ContDiffOn ℝ q h {p | p.1 ∈ I}) :
    ContDiffOn ℝ q (fun a : Z × E ↦ OAI.Analysis.Calculus.SmoothExtension.vectorPeriodization L (fun x ↦ h (a.1, x)) a.2)
      {p | p.1 ∈ I} := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  apply ParameterDeformation.contDiffAt_parametricPeriodization L hL hK h hs p
  intro z
  exact (hh (p.1, p.2 + L z) hp).contDiffAt
    ((hI.preimage continuous_fst).mem_nhds hp)

theorem contDiff_parametricPeriodization
    (L : T →+ E) (hL : ∀ R : ℝ, {z : T | ‖L z‖ ≤ R}.Finite)
    {K : Set E} (hK : IsCompact K) (h : Z × E → E)
    (hs : ∀ t x, x ∉ K → h (t, x) = 0) {q : ℕ∞ω}
    (hh : ContDiff ℝ q h) :
    ContDiff ℝ q (fun a : Z × E ↦ OAI.Analysis.Calculus.SmoothExtension.vectorPeriodization L (fun x ↦ h (a.1, x)) a.2) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  exact ParameterDeformation.contDiffAt_parametricPeriodization L hL hK h hs p (fun _ ↦ hh.contDiffAt)

end ParameterDeformation
end OAI.Analysis.PDE.Dirichlet
