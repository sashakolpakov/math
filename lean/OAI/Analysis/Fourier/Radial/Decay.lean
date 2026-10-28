import Mathlib

/-! Elementary conversion of normalized radial asymptotics to global decay. -/

noncomputable section
namespace OAI.Analysis.Fourier.Radial

theorem abs_cos_sin_combination_le (A B r : ℝ) :
    |A * Real.cos r + B * Real.sin r| ≤ |A| + |B| := by
  calc
    _ ≤ |A * Real.cos r| + |B * Real.sin r| := abs_add_le _ _
    _ = |A| * |Real.cos r| + |B| * |Real.sin r| := by rw [abs_mul, abs_mul]
    _ ≤ |A| * 1 + |B| * 1 := by
      gcongr
      · exact Real.abs_cos_le_one r
      · exact Real.abs_sin_le_one r
    _ = _ := by ring

theorem normalized_asymptotic_bound {r m F A B C : ℝ}
    (hr : 1 ≤ r) (hC : 0 ≤ C)
    (h : |r ^ m * F - (A * Real.cos r + B * Real.sin r)| ≤ C / r) :
    |r ^ m * F| ≤ C + |A| + |B| := by
  have hCr : C / r ≤ C := (div_le_self hC hr)
  calc
    _ = |(r ^ m * F - (A * Real.cos r + B * Real.sin r)) +
        (A * Real.cos r + B * Real.sin r)| := by congr 1; ring
    _ ≤ |r ^ m * F - (A * Real.cos r + B * Real.sin r)| +
        |A * Real.cos r + B * Real.sin r| := abs_add_le _ _
    _ ≤ C + (|A| + |B|) := add_le_add (h.trans hCr) (abs_cos_sin_combination_le A B r)
    _ = _ := by ring

theorem decay_from_normalized_bound {m M D : ℝ} (hm : 0 ≤ m)
    (hM : 0 ≤ M) (hD : 0 ≤ D) {r F : ℝ} (hr : 0 ≤ r)
    (hsmall : |F| ≤ M) (hlarge : 1 ≤ r → |r ^ m * F| ≤ D) :
    |F| ≤ ((M + D + 1) * (2 : ℝ) ^ m) * (1 + r) ^ (-m) := by
  have hp : 0 < (1 + r) ^ m := Real.rpow_pos_of_pos (by linarith) _
  rw [Real.rpow_neg (by linarith : 0 ≤ 1 + r), ← div_eq_mul_inv]
  apply (le_div_iff₀ hp).mpr
  by_cases h : 1 ≤ r
  · have hrp : 0 < r := by linarith
    have hb : (1 + r) ^ m ≤ (2 : ℝ) ^ m * r ^ m := by
      rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hr]
      exact Real.rpow_le_rpow (by linarith) (by linarith) hm
    have hn : |F| * r ^ m ≤ D := by
      simpa only [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hrp m), mul_comm]
        using hlarge h
    calc
      |F| * (1 + r) ^ m ≤ |F| * ((2 : ℝ) ^ m * r ^ m) := by gcongr
      _ = (|F| * r ^ m) * (2 : ℝ) ^ m := by ring
      _ ≤ D * (2 : ℝ) ^ m := by gcongr
      _ ≤ (M + D + 1) * (2 : ℝ) ^ m := by gcongr; linarith
  · have hb : (1 + r) ^ m ≤ (2 : ℝ) ^ m :=
      Real.rpow_le_rpow (by linarith) (by linarith) hm
    calc
      |F| * (1 + r) ^ m ≤ M * (2 : ℝ) ^ m := mul_le_mul hsmall hb
        (Real.rpow_nonneg (by linarith) _) hM
      _ ≤ (M + D + 1) * (2 : ℝ) ^ m := by gcongr; linarith

end OAI.Analysis.Fourier.Radial
