import OAI.Analysis.Fourier.SquareFunction.Radius.Dyadic

/-! The reverse dyadic-radius comparison, used to pass the exact Stein
Plancherel identity to the smooth low-frequency square function. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set
open scoped ENNReal

theorem radius_ratio_dyadic_eq (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∑' k : ℤ, ∫⁻ s in Icc (1 : ℝ) 2, F ((2 : ℝ) ^ k * s) / ENNReal.ofReal s) =
      ∫⁻ r in Ioi (0 : ℝ), F r / ENNReal.ofReal r := by
  have hpow (k : ℤ) : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
    ring
  have hdlt {i j : ℤ} (hij : i < j) :
      Disjoint (Ico ((2 : ℝ) ^ i) ((2 : ℝ) ^ (i + 1)))
        (Ico ((2 : ℝ) ^ j) ((2 : ℝ) ^ (j + 1))) := by
    apply disjoint_left.mpr
    intro r hi hj
    have hp : (2 : ℝ) ^ (i + 1) ≤ (2 : ℝ) ^ j :=
      (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).2 (by omega)
    exact not_lt_of_ge (hp.trans hj.1) hi.2
  have hd : Pairwise (fun i j : ℤ => Disjoint
      (Ico ((2 : ℝ) ^ i) ((2 : ℝ) ^ (i + 1)))
      (Ico ((2 : ℝ) ^ j) ((2 : ℝ) ^ (j + 1)))) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hdlt h
    · exact (hdlt h).symm
  have hu : (⋃ k : ℤ, Ico ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))) = Ioi 0 := by
    ext r
    constructor
    · intro hr
      obtain ⟨k, hk⟩ := mem_iUnion.mp hr
      exact lt_of_lt_of_le (by positivity : 0 < (2 : ℝ) ^ k) hk.1
    · intro hr
      obtain ⟨k, hk⟩ := exists_mem_Ico_zpow hr (by norm_num : (1 : ℝ) < 2)
      exact mem_iUnion.mpr ⟨k, hk⟩
  calc
    _ = ∑' k : ℤ, ∫⁻ r in Ico ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)),
        F r / ENNReal.ofReal r := by
      apply tsum_congr
      intro k
      rw [hpow, restrict_Ico_eq_restrict_Icc,
        setLIntegral_radius_ratio_dilate (by positivity) F hF]
    _ = _ := by rw [← lintegral_iUnion (fun _ => measurableSet_Ico) hd, hu]

theorem radius_dyadic_le_two_ratio (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∑' k : ℤ, ∫⁻ s in Icc (1 : ℝ) 2, F ((2 : ℝ) ^ k * s)) ≤
      2 * ∫⁻ r in Ioi (0 : ℝ), F r / ENNReal.ofReal r := by
  calc
    _ ≤ ∑' k : ℤ, 2 * ∫⁻ s in Icc (1 : ℝ) 2,
        F ((2 : ℝ) ^ k * s) / ENNReal.ofReal s := by
      apply ENNReal.tsum_le_tsum
      intro k
      rw [← lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
      apply setLIntegral_mono' measurableSet_Icc
      intro s hs
      have hs0 : 0 < s := by linarith [hs.1]
      have hs2 : ENNReal.ofReal s ≤ 2 := by
        exact_mod_cast ENNReal.ofReal_le_ofReal hs.2
      calc
        _ = ENNReal.ofReal s * (F ((2 : ℝ) ^ k * s) / ENNReal.ofReal s) := by
          rw [div_eq_mul_inv]
          calc
            _ = F ((2 : ℝ) ^ k * s) *
                (ENNReal.ofReal s * (ENNReal.ofReal s)⁻¹) := by
              rw [ENNReal.mul_inv_cancel (by positivity) ENNReal.ofReal_ne_top, mul_one]
            _ = _ := by ring
        _ ≤ _ := mul_le_mul' hs2 le_rfl
    _ = _ := by rw [ENNReal.tsum_mul_left, radius_ratio_dyadic_eq F hF]

end OAI.Analysis.Fourier.SquareFunction
