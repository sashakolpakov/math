import OAI.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-!
# The exact square-root-logarithm runtime scale

These are numerical definitions and elementary lemmas only.  In particular,
this module supplies no SAT algorithm and makes no computational existence claim.
The logarithms in the target are natural logarithms, including at small inputs.
-/

namespace SubexponentialSAT.SqrtLog.Statement

noncomputable section

/-- The exact scale in the target, with the specified small-input shift. -/
def runtimeScale (n : ℕ) : ℝ :=
  (n : ℝ) * (Real.log (Real.log ((n : ℝ) + 16))) ^ 2 /
    Real.sqrt (Real.log ((n : ℝ) + 16))

theorem two_le_log_shift (n : ℕ) : 2 ≤ Real.log ((n : ℝ) + 16) := by
  have htwo : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  have hpow := Real.log_pow (2 : ℝ) 4
  norm_num at hpow
  have hmon : Real.log 16 ≤ Real.log ((n : ℝ) + 16) :=
    Real.log_le_log (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  linarith

theorem log_shift_pos (n : ℕ) : 0 < Real.log ((n : ℝ) + 16) := by
  have := two_le_log_shift n
  linarith

theorem log_log_shift_pos (n : ℕ) : 0 < Real.log (Real.log ((n : ℝ) + 16)) :=
  Real.log_pos (lt_of_lt_of_le (by norm_num) (two_le_log_shift n))

theorem sqrt_log_shift_pos (n : ℕ) : 0 < Real.sqrt (Real.log ((n : ℝ) + 16)) :=
  Real.sqrt_pos.2 (log_shift_pos n)

theorem runtimeScale_nonneg (n : ℕ) : 0 ≤ runtimeScale n := by
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _))
    (Real.sqrt_nonneg _)

@[simp] theorem runtimeScale_zero : runtimeScale 0 = 0 := by
  simp [runtimeScale]

theorem runtimeScale_pos {n : ℕ} (hn : 0 < n) : 0 < runtimeScale n :=
  div_pos (mul_pos (Nat.cast_pos.2 hn) (sq_pos_of_pos (log_log_shift_pos n)))
    (sqrt_log_shift_pos n)

/-- Constants and polynomial degree are chosen before the input. -/
def runtimeBound (constant exponentConstant : ℝ)
    (degree inputBits numVars : ℕ) : ℝ :=
  constant * ((inputBits : ℝ) + 1) ^ degree *
    (2 : ℝ) ^ (exponentConstant * runtimeScale numVars)

theorem runtimeBound_nonneg {constant : ℝ} (hc : 0 ≤ constant)
    (exponentConstant : ℝ) (degree inputBits numVars : ℕ) :
    0 ≤ runtimeBound constant exponentConstant degree inputBits numVars := by
  unfold runtimeBound
  positivity

theorem runtimeBound_pos {constant : ℝ} (hc : 0 < constant)
    (exponentConstant : ℝ) (degree inputBits numVars : ℕ) :
    0 < runtimeBound constant exponentConstant degree inputBits numVars := by
  unfold runtimeBound
  positivity

theorem runtimeBound_mono_exponent {constant a b : ℝ} (hc : 0 ≤ constant)
    (hab : a ≤ b) (degree inputBits numVars : ℕ) :
    runtimeBound constant a degree inputBits numVars ≤
      runtimeBound constant b degree inputBits numVars := by
  apply mul_le_mul_of_nonneg_left
  · apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact mul_le_mul_of_nonneg_right hab (runtimeScale_nonneg numVars)
  · exact mul_nonneg hc (pow_nonneg (by positivity) degree)

theorem runtimeBound_mul_constant (factor constant exponentConstant : ℝ)
    (degree inputBits numVars : ℕ) :
    runtimeBound (factor * constant) exponentConstant degree inputBits numVars =
      factor * runtimeBound constant exponentConstant degree inputBits numVars := by
  unfold runtimeBound
  ring

/-- A fixed polynomial simulation overhead preserves the specified scale. -/
theorem runtimeBound_pow (constant exponentConstant : ℝ)
    (degree inputBits numVars power : ℕ) :
    runtimeBound constant exponentConstant degree inputBits numVars ^ power =
      runtimeBound (constant ^ power) ((power : ℝ) * exponentConstant)
        (degree * power) inputBits numVars := by
  unfold runtimeBound
  rw [mul_pow, mul_pow, ← pow_mul, ← Real.rpow_mul_natCast (by norm_num)]
  congr 2
  ring

theorem one_le_runtimeBound {constant exponentConstant : ℝ}
    (hc : 1 ≤ constant) (ha : 0 ≤ exponentConstant)
    (degree inputBits numVars : ℕ) :
    1 ≤ runtimeBound constant exponentConstant degree inputBits numVars := by
  unfold runtimeBound
  apply one_le_mul_of_one_le_of_one_le
  · exact one_le_mul_of_one_le_of_one_le hc
      (one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) inputBits; linarith))
  · exact Real.one_le_rpow (by norm_num) (mul_nonneg ha (runtimeScale_nonneg numVars))

end

end SubexponentialSAT.SqrtLog.Statement

end OAI.Algorithms
