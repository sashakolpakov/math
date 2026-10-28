import Mathlib

/-! The radius derivative of the Bochner--Riesz multiplier from `stein_square.tex`. -/

namespace OAI.Analysis.Fourier.SquareFunction

/-- The differentiated multiplier, at a frequency strictly inside the radius. -/
theorem radius_derivative {ρ r : ℝ} (hρ : 0 ≤ ρ) (hr : ρ < r) (α : ℝ) :
    r * deriv (fun s : ℝ => (1 - ρ ^ 2 / s ^ 2) ^ α) r =
      2 * α * (ρ ^ 2 / r ^ 2) * (1 - ρ ^ 2 / r ^ 2) ^ (α - 1) := by
  have hrpos : 0 < r := lt_of_le_of_lt hρ hr
  have hr0 : r ≠ 0 := ne_of_gt hrpos
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr0
  have hbase : 0 < 1 - ρ ^ 2 / r ^ 2 := by
    have : ρ ^ 2 / r ^ 2 < 1 :=
      (div_lt_one (sq_pos_of_pos hrpos)).2 (by nlinarith)
    linarith
  have hpow : HasDerivAt (fun s : ℝ => s ^ 2) (2 * r) r := by
    simpa using hasDerivAt_pow 2 r
  have hquot := (hasDerivAt_const r (ρ ^ 2)).div hpow hr2
  have hdiff := (hasDerivAt_const r (1 : ℝ)).sub hquot
  have hder := hdiff.rpow_const (p := α) (Or.inl (ne_of_gt hbase))
  simp only [Pi.sub_apply, Pi.div_apply] at hder
  rw [hder.deriv]
  field_simp
  ; ring

/-- The differentiated multiplier has exactly the shell factor in the paper. -/
theorem shell_factorization {ρ r : ℝ} (hρ : 0 ≤ ρ) (hr : ρ < r) (α : ℝ) :
    2 * α * (ρ ^ 2 / r ^ 2) * (1 - ρ ^ 2 / r ^ 2) ^ (α - 1) =
      2 * α * ρ ^ 2 * r ^ (-2 * α) * (r + ρ) ^ (α - 1) *
        (r - ρ) ^ (α - 1) := by
  have hrpos : 0 < r := lt_of_le_of_lt hρ hr
  have hr0 : r ≠ 0 := ne_of_gt hrpos
  have hplus : 0 < r + ρ := by linarith
  have hminus : 0 < r - ρ := by linarith
  have hratio : 1 - ρ ^ 2 / r ^ 2 = (r + ρ) * (r - ρ) / r ^ 2 := by
    field_simp
    ; ring
  rw [hratio, Real.div_rpow (mul_nonneg hplus.le hminus.le) (sq_nonneg r),
    Real.mul_rpow hplus.le hminus.le,
    ← Real.rpow_natCast_mul hrpos.le]
  have hpower : r ^ 2 * r ^ ((2 : ℝ) * (α - 1)) = r ^ (2 * α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hrpos]
    congr 1
    ring
  rw [show -2 * α = -(2 * α) by ring, Real.rpow_neg hrpos.le]
  rw [← hpower]
  simp only [Nat.cast_ofNat, mul_inv_rev]
  ring

end OAI.Analysis.Fourier.SquareFunction
