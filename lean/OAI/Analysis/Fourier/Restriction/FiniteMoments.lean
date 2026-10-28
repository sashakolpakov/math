import OAI.Analysis.Fourier.Restriction.Amplitude

open scoped BigOperators
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

/-- The finite counting-measure form of the distribution estimate. -/
theorem finite_card_norm_gt_le {X : Type*} (E : Finset X) (a : X → ℂ)
    {q l : ℝ} (hq : 0 < q) (hl : 0 < l)
    (hsum : (∑ z ∈ E, ‖a z‖ ^ q) ≤ 1) :
    ((E.filter (fun z ↦ l < ‖a z‖)).card : ℝ) ≤ l ^ (-q) := by
  classical
  let S := E.filter (fun z ↦ l < ‖a z‖)
  have H : (S.card : ℝ) * l ^ q ≤ 1 := by
    calc
      _ = ∑ z ∈ S, l ^ q := by simp
      _ ≤ ∑ z ∈ S, ‖a z‖ ^ q := by
        apply Finset.sum_le_sum
        intro z hz
        exact Real.rpow_le_rpow hl.le (Finset.mem_filter.mp hz).2.le hq.le
      _ ≤ ∑ z ∈ E, ‖a z‖ ^ q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro z hz hzs
        positivity
      _ ≤ 1 := hsum
  have HH := (le_div_iff₀ (Real.rpow_pos_of_pos hl q)).mpr H
  simpa only [one_div, Real.rpow_neg hl.le] using HH

theorem finite_norm_le_one_of_sum_rpow_le_one {X : Type*} (E : Finset X) (a : X → ℂ)
    {q : ℝ} (hq : 0 < q) (hsum : (∑ z ∈ E, ‖a z‖ ^ q) ≤ 1)
    {z : X} (hz : z ∈ E) : ‖a z‖ ≤ 1 := by
  have H : ‖a z‖ ^ q ≤ 1 :=
    (Finset.single_le_sum (fun w _ ↦ Real.rpow_nonneg (norm_nonneg _) _) hz).trans hsum
  exact (Real.rpow_le_rpow_iff (norm_nonneg _) (by norm_num) hq).mp
    (by simpa only [Real.one_rpow] using H)

end OAI.Analysis.Fourier.Restriction
