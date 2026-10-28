import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpParameterBounds
import OAI.Algorithms.SubexponentialSAT.SubexpExponentArithmetic

namespace OAI.Algorithms

/-!
# Runtime exponent for the actual growing parameter schedule

This module substitutes the executable prime/packing schedule and the proved
polynomial bounds on all eleven parameters into the counting exponent. No
parameter-growth premise is left to the caller. The numerical cost expression
must still be connected to a program's measured running time separately.
-/

namespace SubexponentialSAT.SubexpScheduleRuntime

open Filter
open SubexpPackingParameters

noncomputable section

/-- The actual packing dimension satisfies the real ceiling inequality. -/
theorem dimension_real_bound {n : ℕ} (hn : GoodInput n) :
    (D n : ℝ) ≤ (n : ℝ) / (ell n : ℝ) + 1 := by
  have hnat := D_le_div_add_one hn
  have hcast : (D n : ℝ) ≤ ((n / ell n : ℕ) : ℝ) + 1 := by exact_mod_cast hnat
  have hdiv : ((n / ell n : ℕ) : ℝ) ≤ (n : ℝ) / (ell n : ℝ) :=
    Nat.cast_div_le
  linarith

theorem capacity_real_lower {n : ℕ} (hn : GoodInput n) :
    (s n : ℝ) / 32 ≤ (ell n : ℝ) := by
  have hnat := s_le_thirtytwo_mul_u hn
  have hreal : (s n : ℝ) ≤ 32 * (ell n : ℝ) := by exact_mod_cast hnat
  linarith

theorem actual_log_bound {n : ℕ} (hn : GoodInput n) :
    Real.logb 2 (p n : ℝ) ≤ (ell n : ℝ) + 1 := by
  have h := SubexpExponentArithmetic.logb_lt_natLog2_add_one (p n)
  rw [log2_p hn] at h
  exact h.le

/-- For each fixed polynomial degree, the actual parameter cost is eventually
bounded by a power of `n+16` with coefficient one. Its degree is chosen before
the input, rather than varying with p, r, Q, or N. -/
theorem eventually_parameter_power (k : ℕ) (hk : 2 ≤ k) (q : ℕ) :
    ∃ d : ℕ, ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
      m ≤ SubexpSchedule.delta k hk n * D n →
      ((SubexpParameterBounds.parameters k hk n m).size : ℝ) ^ q ≤
        ((n : ℝ) + 16) ^ (d : ℝ) := by
  obtain ⟨C, d, hC, hsize⟩ :=
    SubexpParameterBounds.eventually_size_power_polynomial k hk q
  refine ⟨d + 1, ?_⟩
  filter_upwards [hsize, eventually_ge_atTop C] with n hn hCn
  intro m hm
  have hs : ((SubexpParameterBounds.parameters k hk n m).size : ℝ) ^ q ≤
      (C : ℝ) * ((n : ℝ) + 1) ^ d := by exact_mod_cast hn m hm
  have hC' : (C : ℝ) ≤ (n : ℝ) + 16 := by
    have hc : (C : ℝ) ≤ n := by exact_mod_cast hCn
    linarith
  have hp : ((n : ℝ) + 1) ^ d ≤ ((n : ℝ) + 16) ^ d :=
    pow_le_pow_left₀ (by positivity) (by linarith) d
  calc
    ((SubexpParameterBounds.parameters k hk n m).size : ℝ) ^ q ≤
        (C : ℝ) * ((n : ℝ) + 1) ^ d := hs
    _ ≤ ((n : ℝ) + 16) * ((n : ℝ) + 16) ^ d :=
      mul_le_mul hC' hp (by positivity) (by positivity)
    _ = ((n : ℝ) + 16) ^ (d + 1) := by rw [pow_succ]; ring
    _ = ((n : ℝ) + 16) ^ ((d + 1 : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm

/-- Explicit numerical cost after substituting every growing parameter.
The polynomial degree q remains fixed before the input size. -/
def sourceCost (k : ℕ) (hk : 2 ≤ k) (n m q : ℕ) : ℝ :=
  (2 : ℝ) ^ ((n : ℝ) / (s n : ℝ)) *
    (((SubexpParameterBounds.parameters k hk n m).size : ℝ) ^ q * (s n : ℝ) *
      SubexpExponentArithmetic.exponentialPart (p n : ℝ)
        (1 - (1 - 1 / (s n : ℝ)) ^ 2 + 1 / (s n : ℝ)) 128 (D n : ℝ))

/-- The full source counting expression is uniformly subexponential for the
actual schedule. The only input-specific hypothesis is the proved factor-count
bound `m ≤ delta*D`; every growth/rounding/logarithm hypothesis is discharged. -/
theorem eventually_sourceCost_bound (k : ℕ) (hk : 2 ≤ k) (q : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
      m ≤ SubexpSchedule.delta k hk n * D n →
      sourceCost k hk n m q ≤ (2 : ℝ) ^ (A * SubexpComputation.scale n) := by
  obtain ⟨d, hd⟩ := eventually_parameter_power k hk q
  refine ⟨8475 + (d : ℝ), by positivity, ?_⟩
  filter_upwards [hd, eventually_goodInput,
    SubexpExponentArithmetic.eventually_source_cost_le] with n hparam hn hcost
  intro m hm
  have hp : (1 : ℝ) ≤ (p n : ℝ) := by
    have := p_gt_two n
    exact_mod_cast (show 1 ≤ p n by omega)
  have hs : (32 : ℝ) ≤ (s n : ℝ) := by exact_mod_cast hn
  have hellhi : (ell n : ℝ) ≤ (s n : ℝ) := by exact_mod_cast u_le_s n
  exact hcost (p n : ℝ) (ell n : ℝ) (D n : ℝ) (d : ℝ)
    (((SubexpParameterBounds.parameters k hk n m).size : ℝ) ^ q)
    hp hs (capacity_real_lower hn) hellhi (Nat.cast_nonneg _)
    (dimension_real_bound hn) (actual_log_bound hn) (Nat.cast_nonneg _)
    (hparam m hm)

/-- A fixed multiplicative cost and fixed input polynomial may be restored
without changing the uniform exponent obtained above. -/
theorem eventually_source_runtime_bound (k : ℕ) (hk : 2 ≤ k) (q d : ℕ)
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ n : ℕ in atTop, ∀ m L : ℕ,
      m ≤ SubexpSchedule.delta k hk n * D n →
      C * ((L : ℝ) + 1) ^ d * sourceCost k hk n m q ≤
        SubexpComputation.runtimeBound C A d L n := by
  obtain ⟨A, hA, hb⟩ := eventually_sourceCost_bound k hk q
  refine ⟨A, hA, ?_⟩
  filter_upwards [hb] with n hn m L hm
  exact mul_le_mul_of_nonneg_left (hn m hm) (mul_nonneg hC (by positivity))

end
end SubexponentialSAT.SubexpScheduleRuntime

end OAI.Algorithms
