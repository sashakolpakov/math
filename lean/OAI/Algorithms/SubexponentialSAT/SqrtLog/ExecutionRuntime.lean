import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.AsymptoticMonotone

namespace OAI.Algorithms

/-! Numerical closure lemmas for the actual cutoff and identifier wrappers.
These assign no running time to an unimplemented operation. -/
namespace SubexponentialSAT.SqrtLog.Execution

open Statement

theorem input_le_runtimeBound {C A : ℝ} (hC : 1 ≤ C) (hA : 0 ≤ A)
    {d : ℕ} (hd : 0 < d) (L n : ℕ) :
    (L : ℝ)+1 ≤ runtimeBound C A d L n := by
  have hCn : 0 ≤ C := by linarith
  have hbase : (1 : ℝ) ≤ (L : ℝ)+1 := by
    have := Nat.cast_nonneg (α := ℝ) L
    linarith
  have hp := le_self_pow₀ hbase (Nat.ne_of_gt hd)
  have he : (1 : ℝ) ≤ (2 : ℝ)^(A*runtimeScale n) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg hA (runtimeScale_nonneg n))
  calc
    (L : ℝ)+1 ≤ ((L : ℝ)+1)^d := hp
    _ ≤ C*((L : ℝ)+1)^d := le_mul_of_one_le_left (by positivity) hC
    _ ≤ runtimeBound C A d L n := le_mul_of_one_le_right (by positivity) he

theorem runtimeBound_mono_degree {C A : ℝ} (hC : 0 ≤ C)
    {d e : ℕ} (hde : d ≤ e) (L n : ℕ) :
    runtimeBound C A d L n ≤ runtimeBound C A e L n := by
  unfold runtimeBound
  have hbase : (1 : ℝ) ≤ (L : ℝ)+1 := by
    have := Nat.cast_nonneg (α := ℝ) L
    linarith
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase hde) hC)
    (by positivity)

theorem runtimeBound_input_substitution {C A H : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hH : 0 ≤ H)
    (d e L M n m : ℕ) (hsize : (M : ℝ)+1 ≤ H*((L : ℝ)+1)^e)
    (hn : m ≤ n) :
    runtimeBound C A d M m ≤ runtimeBound (C*H^d) A (e*d) L n := by
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (M : ℝ)+1) hsize d
  have he : (2 : ℝ)^(A*runtimeScale m) ≤ (2 : ℝ)^(A*runtimeScale n) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_left (Asymptotic.runtimeScale_mono hn) hA)
  unfold runtimeBound
  calc
    C*((M : ℝ)+1)^d*(2 : ℝ)^(A*runtimeScale m) ≤
        C*(H*((L : ℝ)+1)^e)^d*(2 : ℝ)^(A*runtimeScale n) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hp hC) he (by positivity) (by positivity)
    _ = _ := by rw [mul_pow,← pow_mul]; ring

/-- Rounding is used only for a proof-side time bound, never to supply code. -/
theorem ceil_runtimeBound_le {C A : ℝ} (hC : 1 ≤ C) (hA : 0 ≤ A)
    (d L n : ℕ) :
    (Nat.ceil (runtimeBound C A d L n) : ℝ) ≤ 2*runtimeBound C A d L n := by
  have h := one_le_runtimeBound hC hA d L n
  have hc := Nat.ceil_lt_add_one (show 0 ≤ runtimeBound C A d L n by linarith)
  linarith

/-- Exactly the source time paid by ExecutionCompletion, including the real
small-input scanner and a rounded bound on the large-input controller. -/
theorem cutoff_source_bound {C A : ℝ} (hC : 1 ≤ C) (hA : 0 ≤ A)
    {d : ℕ} (hd : 0 < d) (N L n : ℕ) :
    ((6*N+3*L+Nat.ceil (runtimeBound C A d L n)+12 : ℕ) : ℝ) ≤
      runtimeBound (((6*N+17 : ℕ) : ℝ)*C) A d L n := by
  have hi := input_le_runtimeBound hC hA hd L n
  have h1 := one_le_runtimeBound hC hA d L n
  have ht := ceil_runtimeBound_le hC hA d L n
  have hfixed : 6*(N : ℝ)+12 ≤
      (6*(N : ℝ)+12)*runtimeBound C A d L n :=
    le_mul_of_one_le_right (by positivity) h1
  rw [runtimeBound_mul_constant]
  push_cast
  nlinarith

end SubexponentialSAT.SqrtLog.Execution

end OAI.Algorithms
