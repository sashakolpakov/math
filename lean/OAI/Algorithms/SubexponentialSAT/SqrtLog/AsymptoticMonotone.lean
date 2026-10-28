import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.StatementScale

namespace OAI.Algorithms

/-! Exact monotonicity of the stated runtime scale, including unused ambient
variables. These lemmas concern numbers, not a change in the input encoding. -/

namespace SubexponentialSAT.SqrtLog.Asymptotic

theorem mul_log_shift_le {a b : ℕ} (hab : a ≤ b) :
    (a : ℝ) * Real.log ((b : ℝ) + 16) ≤
      (b : ℝ) * Real.log ((a : ℝ) + 16) := by
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have ha : 0 < (a : ℝ) + 16 := by positivity
  have hb : 0 < (b : ℝ) + 16 := by positivity
  have hd : 0 ≤ Real.log ((b : ℝ) + 16) - Real.log ((a : ℝ) + 16) := by
    have h := Real.log_le_log ha (show (a : ℝ) + 16 ≤ (b : ℝ) + 16 by linarith)
    linarith
  have h := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne'] at h
  have hm : (Real.log ((b : ℝ) + 16) - Real.log ((a : ℝ) + 16) + 1) *
      ((a : ℝ) + 16) ≤ (b : ℝ) + 16 :=
    (le_div_iff₀ ha).mp (by linarith)
  have hla := Statement.two_le_log_shift a
  have hprod := mul_nonneg (sub_nonneg.mpr hab')
    (show 0 ≤ Real.log ((a : ℝ) + 16) - 1 by linarith)
  nlinarith

theorem div_sqrt_log_shift_mono {a b : ℕ} (hab : a ≤ b) :
    (a : ℝ) / Real.sqrt (Real.log ((a : ℝ) + 16)) ≤
      (b : ℝ) / Real.sqrt (Real.log ((b : ℝ) + 16)) := by
  have ha := Statement.sqrt_log_shift_pos a
  have hb := Statement.sqrt_log_shift_pos b
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hlog := mul_log_shift_le hab
  have ham := Real.sq_sqrt (Statement.log_shift_pos a).le
  have hbm := Real.sq_sqrt (Statement.log_shift_pos b).le
  have hsq : ((a : ℝ) * Real.sqrt (Real.log ((b : ℝ) + 16))) ^ 2 ≤
      ((b : ℝ) * Real.sqrt (Real.log ((a : ℝ) + 16))) ^ 2 := by
    rw [mul_pow, mul_pow, ham, hbm]
    have hm := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg a)
    have hn := mul_nonneg (show (0 : ℝ) ≤ b - a by linarith)
      (mul_nonneg (Nat.cast_nonneg b) (Statement.log_shift_pos a).le)
    nlinarith
  apply (div_le_div_iff₀ ha hb).2
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq

theorem runtimeScale_mono : Monotone Statement.runtimeScale := by
  intro a b hab
  have hbase := div_sqrt_log_shift_mono hab
  have hinner : Real.log ((a : ℝ) + 16) ≤ Real.log ((b : ℝ) + 16) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast Nat.add_le_add_right hab 16
  have houter := Real.log_le_log (Statement.log_shift_pos a) hinner
  have hpow := pow_le_pow_left₀ (Statement.log_log_shift_pos a).le houter 2
  have hm := mul_le_mul hbase hpow (sq_nonneg _)
    (div_nonneg (Nat.cast_nonneg b) (Statement.sqrt_log_shift_pos b).le)
  simpa only [Statement.runtimeScale, div_mul_eq_mul_div] using hm

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
