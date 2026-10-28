import OAI.Analysis.Fourier.SquareFunction.Summation

/-! Dyadic shell widths and the summable numerical losses at the strict
Stein threshold. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory
open scoped ENNReal

noncomputable def dyadicShellWidth (J j : ℕ) : ℝ :=
  (2 : ℝ) ^ (-((J + j : ℕ) : ℝ))

theorem dyadicShellWidth_pos (J j : ℕ) : 0 < dyadicShellWidth J j :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem dyadicShellWidth_le_one (J j : ℕ) : dyadicShellWidth J j ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.mpr (Nat.cast_nonneg _))

theorem inv_dyadicShellWidth (J j : ℕ) :
    (dyadicShellWidth J j)⁻¹ = (2 : ℝ) ^ (J + j) := by
  rw [dyadicShellWidth, Real.rpow_neg (by norm_num), inv_inv, Real.rpow_natCast]

theorem rpow_dyadicShellWidth (J j : ℕ) (d : ℝ) :
    dyadicShellWidth J j ^ d = (2 : ℝ) ^ (-((J + j : ℕ) : ℝ) * d) := by
  rw [dyadicShellWidth, ← Real.rpow_mul (by norm_num)]

theorem log_one_div_dyadicShellWidth (J j : ℕ) :
    Real.log (1 / dyadicShellWidth J j) = ((J + j : ℕ) : ℝ) * Real.log 2 := by
  rw [one_div, inv_dyadicShellWidth, Real.log_pow]

theorem summable_dyadicShellWidth_log {d θ : ℝ} (hd : 0 < d) (hθ : 0 ≤ θ) (J : ℕ) :
    Summable (fun j : ℕ => dyadicShellWidth J j ^ d *
      (1 + Real.log (1 / dyadicShellWidth J j)) ^ θ) := by
  have hs := (summable_nat_add_iff (f := fun j : ℕ =>
    (2 : ℝ) ^ (-(j : ℝ) * d) * (1 + (j : ℝ)) ^ θ) J).2 (summable_shell_weights hd θ)
  have hmajor : Summable (fun j : ℕ => (2 : ℝ) ^ (-((J + j : ℕ) : ℝ) * d) *
      (1 + ((J + j : ℕ) : ℝ)) ^ θ) := by
    simpa only [Nat.add_comm] using hs
  apply Summable.of_nonneg_of_le (fun j => by
    apply mul_nonneg (Real.rpow_nonneg (dyadicShellWidth_pos J j).le _)
    apply Real.rpow_nonneg
    have h := Real.log_nonneg ((one_le_div (dyadicShellWidth_pos J j)).mpr
      (dyadicShellWidth_le_one J j))
    linarith) _ hmajor
  intro j
  rw [rpow_dyadicShellWidth, log_one_div_dyadicShellWidth]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow _ _ hθ
  · have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    positivity
  · have hlog : Real.log 2 ≤ 1 := by
      convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1 ; norm_num
    nlinarith [Nat.cast_nonneg (α := ℝ) (J + j)]

end OAI.Analysis.Fourier.SquareFunction
