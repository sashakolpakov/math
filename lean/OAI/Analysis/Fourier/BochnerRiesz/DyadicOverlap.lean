import OAI.Analysis.Fourier.BochnerRiesz.LittlewoodPaleyL2
import Mathlib.Data.Int.Interval

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped BigOperators
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem dyadic_band_index_range {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} {k j : ℤ} {ξ : E}
    (hk : (2 : ℝ) ^ (-(N : ℤ)) ≤ ‖(2 : ℝ) ^ (-k) • ξ‖)
    (hj : ‖(2 : ℝ) ^ (-j) • ξ‖ ≤ (2 : ℝ) ^ (N : ℤ)) :
    k ≤ j + 2 * (N : ℤ) := by
  have hn (i : ℤ) : ‖(2 : ℝ) ^ (-i) • ξ‖ = (2 : ℝ) ^ (-i) * ‖ξ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (zpow_pos (by norm_num) _)]
  rw [hn] at hk hj
  have hl : (2 : ℝ) ^ (k - N) ≤ ‖ξ‖ := by
    calc
      _ = (2 : ℝ) ^ k * (2 : ℝ) ^ (-(N : ℤ)) := by
        rw [← zpow_add₀ (by norm_num)]; congr 1
      _ ≤ (2 : ℝ) ^ k * ((2 : ℝ) ^ (-k) * ‖ξ‖) :=
        mul_le_mul_of_nonneg_left hk (le_of_lt (zpow_pos (by norm_num) _))
      _ = ‖ξ‖ := by rw [← mul_assoc, ← zpow_add₀ (by norm_num)]; simp
  have hu : ‖ξ‖ ≤ (2 : ℝ) ^ (j + N) := by
    calc
      _ = (2 : ℝ) ^ j * ((2 : ℝ) ^ (-j) * ‖ξ‖) := by
        rw [← mul_assoc, ← zpow_add₀ (by norm_num)]; simp
      _ ≤ (2 : ℝ) ^ j * (2 : ℝ) ^ (N : ℤ) :=
        mul_le_mul_of_nonneg_left hj (le_of_lt (zpow_pos (by norm_num) _))
      _ = _ := (zpow_add₀ (by norm_num) _ _).symm
  have h := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp (hl.trans hu)
  omega

theorem card_dyadic_annular_support_le {n N : ℕ} (χ : Space n → ℂ)
    (hband : ∀ ξ, χ ξ ≠ 0 →
      (2 : ℝ) ^ (-(N : ℤ)) ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ (2 : ℝ) ^ (N : ℤ))
    (s : Finset ℤ) (ξ : Space n) :
    (s.filter (fun k ↦ χ ((2 : ℝ) ^ (-k) • ξ) ≠ 0)).card ≤ 2 * N + 1 := by
  classical
  let a := s.filter (fun k ↦ χ ((2 : ℝ) ^ (-k) • ξ) ≠ 0)
  change a.card ≤ _
  rcases a.eq_empty_or_nonempty with he | he
  · simp [he]
  let j := a.min' he
  have hj : j ∈ a := Finset.min'_mem a he
  have hsub : a ⊆ Finset.Icc j (j + 2 * (N : ℤ)) := by
    intro k hk
    apply Finset.mem_Icc.mpr
    refine ⟨Finset.min'_le a k hk, ?_⟩
    exact dyadic_band_index_range
      (hband _ (Finset.mem_filter.mp hk).2).1
      (hband _ (Finset.mem_filter.mp hj).2).2
  calc
    _ ≤ (Finset.Icc j (j + 2 * (N : ℤ))).card := Finset.card_le_card hsub
    _ = 2 * N + 1 := by rw [Int.card_Icc]; omega

theorem sum_sq_dyadic_annular_symbol_le {n N : ℕ} (χ : Space n → ℂ)
    (hband : ∀ ξ, χ ξ ≠ 0 →
      (2 : ℝ) ^ (-(N : ℤ)) ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ (2 : ℝ) ^ (N : ℤ))
    {M : ℝ} (_ : 0 ≤ M) (hbound : ∀ ξ, ‖χ ξ‖ ≤ M)
    (s : Finset ℤ) (ξ : Space n) :
    ∑ k ∈ s, ‖χ ((2 : ℝ) ^ (-k) • ξ)‖ ^ 2 ≤ (2 * (N : ℝ) + 1) * M ^ 2 := by
  classical
  let a := s.filter (fun k ↦ χ ((2 : ℝ) ^ (-k) • ξ) ≠ 0)
  have he : (∑ k ∈ s, ‖χ ((2 : ℝ) ^ (-k) • ξ)‖ ^ 2) =
      ∑ k ∈ a, ‖χ ((2 : ℝ) ^ (-k) • ξ)‖ ^ 2 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk hka
    have hz : χ ((2 : ℝ) ^ (-k) • ξ) = 0 := by
      by_contra hn
      exact hka (Finset.mem_filter.mpr ⟨hk, hn⟩)
    rw [hz]
    norm_num
  rw [he]
  calc
    _ ≤ ∑ k ∈ a, M ^ 2 := by
      apply Finset.sum_le_sum
      intro k _
      exact pow_le_pow_left₀ (norm_nonneg _) (hbound _) 2
    _ = (a.card : ℝ) * M ^ 2 := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact_mod_cast card_dyadic_annular_support_le χ hband s ξ

end OAI.Analysis.Fourier.BochnerRiesz
