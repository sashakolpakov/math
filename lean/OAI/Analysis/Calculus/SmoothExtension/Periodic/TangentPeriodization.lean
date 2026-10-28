import OAI.Analysis.Calculus.SmoothExtension.Periodic.Extension.Lattice

noncomputable section
open Set Filter Metric Module
open scoped Topology ContDiff
namespace OAI.Analysis.Calculus.SmoothExtension

variable {E F T : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [AddCommGroup T]

def vectorPeriodization (L : T →+ E) (f : E → F) (x : E) : F :=
  ∑' z, f (x + L z)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem locallyFinite_vector_translates (L : T →+ E)
    (hL : ∀ R : ℝ, {z : T | ‖L z‖ ≤ R}.Finite)
    {f : E → F} (hc : HasCompactSupport f) :
    LocallyFinite (fun z : T ↦ Function.support (fun x ↦ f (x + L z))) := by
  obtain ⟨R, hR, hb⟩ := hc.isBounded.exists_pos_norm_le
  intro x
  refine ⟨ball x 1, ball_mem_nhds x (by norm_num), ?_⟩
  apply (hL (R + (‖x‖ + 1))).subset
  rintro z ⟨y, hy, hyx⟩
  have hn := hb (y + L z) (subset_tsupport _ hy)
  have hd : ‖y - x‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hyx
  have hny : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by simpa using norm_add_le (y - x) x
  have hz : ‖L z‖ ≤ ‖y + L z‖ + ‖y‖ := by simpa using norm_sub_le (y + L z) y
  change ‖L z‖ ≤ R + (‖x‖ + 1)
  linarith

theorem contDiff_vectorPeriodization (L : T →+ E)
    (hL : ∀ R : ℝ, {z : T | ‖L z‖ ≤ R}.Finite)
    {f : E → F} {q : ℕ∞} (hf : ContDiff ℝ q f) (hc : HasCompactSupport f) :
    ContDiff ℝ q (vectorPeriodization L f) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨U, hU, hfin⟩ := locallyFinite_vector_translates L hL hc x
  have heq : vectorPeriodization L f =ᶠ[𝓝 x]
      (fun y ↦ ∑ z ∈ hfin.toFinset, f (y + L z)) := by
    filter_upwards [hU] with y hy
    apply tsum_eq_sum
    intro z hz
    by_contra hne
    exact hz (hfin.mem_toFinset.mpr ⟨y, hne, hy⟩)
  have hs : ContDiff ℝ q (fun y ↦ ∑ z ∈ hfin.toFinset, f (y + L z)) :=
    ContDiff.sum (fun z _ ↦ hf.comp (contDiff_id.add contDiff_const))
  exact hs.contDiffAt.congr_of_eventuallyEq heq

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem vectorPeriodization_add (L : T →+ E) (f : E → F) (k : T) (x : E) :
    vectorPeriodization L f (x + L k) = vectorPeriodization L f x := by
  classical
  simpa only [vectorPeriodization, Equiv.coe_addRight, map_add, add_assoc, add_comm,
    add_left_comm] using (Equiv.addRight k).tsum_eq (fun z ↦ f (x + L z))

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem vectorPeriodization_eq_self (L : T →+ E) (f : E → F) (x : E)
    (hoff : ∀ z : T, z ≠ 0 → f (x + L z) = 0) :
    vectorPeriodization L f x = f x := by
  classical
  unfold vectorPeriodization
  rw [tsum_eq_single 0 (fun z hz ↦ hoff z hz)]
  simp

omit [NormedSpace ℝ E] in
theorem continuousLinearMap_vectorPeriodization_eq_zero (L : T →+ E)
    (hL : ∀ R : ℝ, {z : T | ‖L z‖ ≤ R}.Finite)
    {f : E → F} (hc : HasCompactSupport f) (A : F →L[ℝ] ℝ) (x : E)
    (hz : ∀ z : T, A (f (x + L z)) = 0) : A (vectorPeriodization L f x) = 0 := by
  classical
  have hs := (locallyFinite_vector_translates L hL hc).point_finite x
  have heq : vectorPeriodization L f x = ∑ z ∈ hs.toFinset, f (x + L z) := by
    apply tsum_eq_sum
    intro z hz
    by_contra hn
    exact hz (hs.mem_toFinset.mpr hn)
  rw [heq, map_sum]
  simp only [hz, Finset.sum_const_zero]

omit [NormedSpace ℝ E] in
/-- A discrete injective period group has a uniform gap from zero. -/
theorem exists_positive_period_gap (L : T →+ E) (hLi : Function.Injective L)
    (hL : ∀ R : ℝ, {z : T | ‖L z‖ ≤ R}.Finite) :
    ∃ d : ℝ, 0 < d ∧ ∀ z : T, z ≠ 0 → d ≤ ‖L z‖ := by
  classical
  have hfinite (s : Finset T) : ∃ d : ℝ, 0 < d ∧ ∀ z ∈ s, z ≠ 0 → d ≤ ‖L z‖ := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨d, hd, hs⟩ := ih
      by_cases haz : a = 0
      · refine ⟨d, hd, ?_⟩
        intro z hz hn
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact (hn haz).elim
        · exact hs z hz hn
      · have hna : 0 < ‖L a‖ := norm_pos_iff.mpr (by
          intro h
          exact haz (hLi (h.trans (map_zero L).symm)))
        refine ⟨min d ‖L a‖, lt_min hd hna, ?_⟩
        intro z hz hn
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact min_le_right _ _
        · exact (min_le_left _ _).trans (hs z hz hn)
  obtain ⟨d, hd, hs⟩ := hfinite (hL 1).toFinset
  refine ⟨min d 1, lt_min hd zero_lt_one, ?_⟩
  intro z hz
  by_cases hn : ‖L z‖ ≤ 1
  · exact (min_le_left _ _).trans (hs z ((hL 1).mem_toFinset.mpr hn) hz)
  · exact (min_le_right _ _).trans (le_of_not_ge hn)

end OAI.Analysis.Calculus.SmoothExtension
