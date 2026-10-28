import Mathlib

open Set Filter
open scoped ContDiff Topology
noncomputable section

namespace OAI.Analysis.PDE.Variational

variable {E T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [AddCommGroup T]

def discretePeriodization (L : T →+ E) (φ : E → ℝ) (x : E) : ℝ :=
  ∑' z, φ (x + L z)

omit [NormedSpace ℝ E] in
theorem locallyFinite_discrete_translates (L : T →+ E)
    (hL : ∀ R : ℝ, {z : T | ‖L z‖ ≤ R}.Finite)
    {φ : E → ℝ} (hφ : HasCompactSupport φ) :
    LocallyFinite (fun z : T ↦ Function.support (fun x ↦ φ (x + L z))) := by
  obtain ⟨R, hR, hbound⟩ := hφ.isBounded.exists_pos_norm_le
  intro x
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x (by norm_num), ?_⟩
  apply (hL (R + (‖x‖+1))).subset
  rintro z ⟨y, hy, hyx⟩
  have hnorm := hbound (y + L z) (subset_tsupport _ hy)
  have hxy : ‖y-x‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hyx
  have hny : ‖y‖ ≤ ‖y-x‖ + ‖x‖ := by
    simpa only [sub_add_cancel] using norm_add_le (y-x) x
  have hz : ‖L z‖ ≤ ‖y+L z‖ + ‖y‖ := by
    simpa only [add_sub_cancel_left] using norm_sub_le (y+L z) y
  change ‖L z‖ ≤ R + (‖x‖+1)
  linarith

theorem contDiff_discretePeriodization (L : T →+ E)
    (hL : ∀ R : ℝ, {z : T | ‖L z‖ ≤ R}.Finite)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ContDiff ℝ ∞ (discretePeriodization L φ) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨U, hU, hfin⟩ := locallyFinite_discrete_translates L hL hc x
  have heq : discretePeriodization L φ =ᶠ[𝓝 x]
      (fun y ↦ ∑ z ∈ hfin.toFinset, φ (y + L z)) := by
    filter_upwards [hU] with y hy
    apply tsum_eq_sum
    intro z hz
    by_contra hne
    exact hz (hfin.mem_toFinset.mpr ⟨y, hne, hy⟩)
  have hs : ContDiff ℝ ∞ (fun y ↦ ∑ z ∈ hfin.toFinset, φ (y + L z)) :=
    ContDiff.sum (fun z _ ↦ hφ.comp (contDiff_id.add contDiff_const))
  exact hs.contDiffAt.congr_of_eventuallyEq heq

omit [NormedSpace ℝ E] in
theorem discretePeriodization_add (L : T →+ E) (φ : E → ℝ) (k : T) (x : E) :
    discretePeriodization L φ (x + L k) = discretePeriodization L φ x := by
  classical
  simpa only [discretePeriodization, Equiv.coe_addRight, map_add, add_assoc, add_comm,
    add_left_comm] using (Equiv.addRight k).tsum_eq (fun z ↦ φ (x + L z))

omit [NormedSpace ℝ E] in
theorem discretePeriodization_eq_self (L : T →+ E) (φ : E → ℝ) (x : E)
    (hoff : ∀ z : T, z ≠ 0 → φ (x + L z) = 0) :
    discretePeriodization L φ x = φ x := by
  classical
  unfold discretePeriodization
  rw [tsum_eq_single 0 (fun z hz ↦ hoff z hz)]
  simp

end OAI.Analysis.PDE.Variational
