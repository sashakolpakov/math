import OAI.Analysis.Fourier.Restriction.FiniteLp

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal BigOperators
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem sparse_balls_disjoint {n N : ℕ} (hn : 2 ≤ n) {R : ℝ} (hR : 1 ≤ R)
    (z : Fin N → Space n)
    (hsep : ∀ i j, i ≠ j → R ^ (16 * n) * (N : ℝ) ^ (16 * n) ≤ dist (z i) (z j)) :
    Pairwise (fun i j ↦ Disjoint (ball (z i) R) (ball (z j) R)) := by
  intro i j hij
  have hN : 2 ≤ N := by
    have hi := i.isLt
    have hj := j.isLt
    have hne : i.val ≠ j.val := fun h ↦ hij (Fin.ext h)
    omega
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hD : 1 ≤ 16 * n := by omega
  have hpowR : R ≤ R ^ (16 * n) := by
    simpa only [pow_one] using pow_le_pow_right₀ hR hD
  have hpowN : (N : ℝ) ≤ (N : ℝ) ^ (16 * n) := by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ N) hD
  have hdist : 2 * R ≤ dist (z i) (z j) := by
    apply le_trans _ (hsep i j hij)
    nlinarith [mul_le_mul hpowR hpowN (by linarith : (0 : ℝ) ≤ N) (by positivity : 0 ≤ R ^ (16 * n))]
  rw [Set.disjoint_left]
  intro x hxi hxj
  have H := dist_triangle (z i) x (z j)
  have hxi' : dist (z i) x < R := by simpa only [mem_ball, dist_comm] using hxi
  have hxj' : dist x (z j) < R := hxj
  linarith

theorem sum_ball_indicators_eq {n N : ℕ} (z : Fin N → Space n) (R : ℝ)
    (hd : Pairwise (fun i j ↦ Disjoint (ball (z i) R) (ball (z j) R)))
    (f : Space n → ℂ) (hs : ∀ x, (∀ i, x ∉ ball (z i) R) → f x = 0) (x : Space n) :
    ∑ i, (ball (z i) R).indicator f x = f x := by
  classical
  by_cases hex : ∃ i, x ∈ ball (z i) R
  · obtain ⟨i, hi⟩ := hex
    rw [Finset.sum_eq_single i]
    · exact indicator_of_mem hi f
    · intro j hj hji
      exact indicator_of_notMem (fun h ↦ Set.disjoint_left.mp (hd hji) h hi) f
    · simp
  · have hh : ∀ i, x ∉ ball (z i) R := by simpa only [not_exists] using hex
    simp only [indicator_of_notMem (hh _), Finset.sum_const_zero, hs x hh]

theorem sum_indicator_enorm_rpow_le {X : Type*} {N : ℕ} (s : Fin N → Set X)
    (hd : Pairwise (fun i j ↦ Disjoint (s i) (s j))) (f : X → ℂ)
    {p : ℝ} (hp : 0 < p) (x : X) :
    ∑ i, ‖(s i).indicator f x‖ₑ ^ p ≤ ‖f x‖ₑ ^ p := by
  classical
  by_cases hex : ∃ i, x ∈ s i
  · obtain ⟨i, hi⟩ := hex
    rw [Finset.sum_eq_single i]
    · rw [indicator_of_mem hi]
    · intro j hj hji
      rw [indicator_of_notMem (fun h ↦ Set.disjoint_left.mp (hd hji) h hi), enorm_zero,
        ENNReal.zero_rpow_of_pos hp]
    · simp
  · have hh : ∀ i, x ∉ s i := by simpa only [not_exists] using hex
    simp only [indicator_of_notMem (hh _), enorm_zero, ENNReal.zero_rpow_of_pos hp,
      Finset.sum_const_zero]
    exact bot_le

end OAI.Analysis.Fourier.Restriction
