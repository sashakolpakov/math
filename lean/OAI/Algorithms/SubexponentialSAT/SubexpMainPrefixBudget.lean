import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainVisitBounds

namespace OAI.Algorithms

/-! Convert the real-valued uniform estimate to one natural-number prefix
budget for the actual leaf contract. Rounding adds only a constant factor. -/

namespace SubexponentialSAT.SubexpMainPrefixBudget

open SubexpComputation

noncomputable def limit (C A : ℝ) (d L n : ℕ) : List Bool → ℕ :=
  fun _ => Nat.ceil (runtimeBound C A d L n)

theorem of_le {C A : ℝ} {d L n steps : ℕ} (bits : List Bool)
    (h : (steps : ℝ) ≤ runtimeBound C A d L n) :
    steps ≤ limit C A d L n bits := by
  exact_mod_cast h.trans (Nat.le_ceil (runtimeBound C A d L n))

theorem limit_le {C A : ℝ} {d L n : ℕ} (hC : 1 ≤ C) (hA : 0 ≤ A)
    (bits : List Bool) :
    (limit C A d L n bits : ℝ) ≤ runtimeBound (2 * C) A d L n := by
  have hP := one_le_runtimeBound hC hA d L n
  have hceil := Nat.ceil_lt_add_one (le_trans (by norm_num : (0 : ℝ) ≤ 1) hP)
  change (Nat.ceil (runtimeBound C A d L n) : ℝ) ≤ _
  rw [runtimeBound_mul_constant]
  nlinarith

theorem sum_three {C A : ℝ} {d L n first second third : ℕ}
    (hfirst : (first : ℝ) ≤ runtimeBound C A d L n)
    (hsecond : (second : ℝ) ≤ runtimeBound C A d L n)
    (hthird : (third : ℝ) ≤ runtimeBound C A d L n) :
    ((first + second + third : ℕ) : ℝ) ≤ runtimeBound (3 * C) A d L n := by
  rw [runtimeBound_mul_constant]
  push_cast
  linarith

/-- This is a proof-side budget only. The machine executes the actual
stages; it does not compute a real exponential or its ceiling. -/
theorem three_stage_limit {C A : ℝ} {d L n first second third : ℕ}
    (bits : List Bool)
    (hfirst : (first : ℝ) ≤ runtimeBound C A d L n)
    (hsecond : (second : ℝ) ≤ runtimeBound C A d L n)
    (hthird : (third : ℝ) ≤ runtimeBound C A d L n) :
    first + second + third ≤ limit (3 * C) A d L n bits :=
  of_le bits (sum_three hfirst hsecond hthird)

end SubexponentialSAT.SubexpMainPrefixBudget

end OAI.Algorithms
