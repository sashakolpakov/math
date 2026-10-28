import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpScheduleRuntime
import OAI.Algorithms.SubexponentialSAT.SubexpLayoutSpec
import OAI.Algorithms.SubexponentialSAT.DyadicSchedule

namespace OAI.Algorithms

/-!
# Scheduled bounds for the actual layout's enumeration counts

These bounds use the implemented prime, chunk dimension, color count and
reciprocal tolerance. They do not identify the dyadic sparsification schedule
with the older threshold search. Any fixed powers introduced by measured
program costs remain explicit in the final exponent.
-/

namespace SubexponentialSAT.SubexpMainIterationBounds

open Filter SubexpPackingParameters SubexpComputation

noncomputable def iterationEnvelope (n : ℕ) : ℝ :=
  (r n : ℝ) * (p n : ℝ) ^
    (SubexpCosetCount.alpha (r n) (1 / (s n : ℝ)) * (D n : ℝ))

theorem dimension_le_scale {n : ℕ} (hn : GoodInput n) :
    (D n : ℝ) ≤ 66 * scale n := by
  have hsn : (s n : ℝ) ≤ n := by exact_mod_cast s_le_n n
  have hs : (32 : ℝ) ≤ s n := by exact_mod_cast hn
  have hd := SubexpExponentArithmetic.dimension_le hs hsn
    (SubexpScheduleRuntime.capacity_real_lower hn)
    (SubexpScheduleRuntime.dimension_real_bound hn)
  have hn16 : 16 ≤ n := by have := s_le_n n; dsimp [GoodInput] at hn; omega
  have hr := SubexpExponentArithmetic.natLog2_ratio_le_twice_scale hn16
  change (n : ℝ) / (s n : ℝ) ≤ 2 * scale n at hr
  linarith

theorem eventually_iterationEnvelope :
    ∀ᶠ n : ℕ in atTop, iterationEnvelope n ≤ (2 : ℝ) ^ (25 * scale n) := by
  filter_upwards [eventually_goodInput,
    SubexpExponentArithmetic.eventually_logb_le_scale_nat] with n hn hlogn
  have hp : (1 : ℝ) ≤ p n := by exact_mod_cast (p_prime n).one_lt.le
  have hs : (32 : ℝ) ≤ s n := by exact_mod_cast hn
  have hsn : (s n : ℝ) ≤ n := by exact_mod_cast s_le_n n
  have hell : (ell n : ℝ) ≤ s n := by exact_mod_cast u_le_s n
  have hn16 : 16 ≤ n := by have := s_le_n n; dsimp [GoodInput] at hn; omega
  have h := SubexpExponentArithmetic.parameter_cost_le
    (p := (p n : ℝ)) (n := (n : ℝ)) (s := (s n : ℝ))
    (ell := (ell n : ℝ)) (D := (D n : ℝ))
    (alpha := 1 - (1 - 1 / (s n : ℝ)) ^ 2 + 1 / (s n : ℝ))
    (c := 0) (d := 0) (r := (r n : ℝ)) (H := 1)
    hp hs hsn (SubexpScheduleRuntime.capacity_real_lower hn) hell
    (Nat.cast_nonneg _) (SubexpScheduleRuntime.dimension_real_bound hn)
    (SubexpScheduleRuntime.actual_log_bound hn)
    (SubexpExponentArithmetic.alpha_le_three_div _) (by norm_num) (by norm_num)
    (Nat.cast_nonneg _) (by dsimp [r]; linarith) (by simp)
    (SubexpExponentArithmetic.natLog2_ratio_le_twice_scale hn16) hlogn
  simpa only [iterationEnvelope, SubexpCosetCount.alpha, r,
    SubexpExponentArithmetic.exponentialPart, zero_mul, Real.rpow_zero,
    mul_one, one_mul, mul_zero, add_zero, SubexpComputation.scale,
    SubexpComputation.logLog, SubexpExponentArithmetic.scale,
    SubexpExponentArithmetic.shiftedLogLog,
    show (2 : ℝ) * 12 + 1 = 25 by norm_num] using h

theorem layout_iteration {n k Δ : ℕ} [Fact (p n).Prime]
    {E : Type*} [Field E] [Algebra (ZMod (p n)) E]
    {F : Type*} [Fintype F] {P : Factor.Pattern (Fin (D n)) F}
    {c : SubexpLayoutSpec.Parameters (p n) k Δ (r n) (DyadicSchedule.tau n)}
    (layout : SubexpLayoutSpec.Layout (E := E) P c)
    (t : Fin c.Q) : (Nat.card (layout.Iterations t) : ℝ) ≤ iterationEnvelope n := by
  simpa only [iterationEnvelope, DyadicSchedule.tau, Rat.cast_div,
    Rat.cast_one, Rat.cast_natCast, Fintype.card_fin] using layout.iteration_bound t

theorem enumeration_iteration {n k Δ : ℕ} [Fact (p n).Prime]
    {E : Type*} [Field E] [Algebra (ZMod (p n)) E]
    {F : Type*} [Fintype F] {P : Factor.Pattern (Fin (D n)) F}
    {c : SubexpLayoutSpec.Parameters (p n) k Δ (r n) (DyadicSchedule.tau n)}
    (layout : SubexpLayoutSpec.Layout (E := E) P c)
    {t : Fin c.Q} (data : SubexpLayoutSpec.EnumerationData layout t) :
    (data.iterationCount : ℝ) ≤ iterationEnvelope n := by
  simpa only [iterationEnvelope, DyadicSchedule.tau, Rat.cast_div,
    Rat.cast_one, Rat.cast_natCast, Fintype.card_fin] using data.iterationCount_bound

/-- Fixed powers of the actual enumeration count and dense-polynomial
overhead still fit the exact n/loglog(n) scale, with explicit coefficients. -/
theorem eventually_power_bound (q : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    ∀ᶠ n : ℕ in atTop, ∀ I : ℕ, (I : ℝ) ≤ iterationEnvelope n →
      (I : ℝ) ^ q * (2 : ℝ) ^ (c * (D n : ℝ)) ≤
        (2 : ℝ) ^ ((25 * (q : ℝ) + 66 * c) * scale n) := by
  filter_upwards [eventually_goodInput, eventually_iterationEnvelope] with n hn hi
  intro I hI
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg I) (hI.trans hi) q
  have hdim := mul_le_mul_of_nonneg_left (dimension_le_scale hn) hc
  have hexp : (2 : ℝ) ^ (c * (D n : ℝ)) ≤ (2 : ℝ) ^ ((66 * c) * scale n) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith only [hdim]
  calc
    _ ≤ ((2 : ℝ) ^ (25 * scale n)) ^ q * (2 : ℝ) ^ ((66 * c) * scale n) :=
      mul_le_mul hpow hexp (by positivity) (by positivity)
    _ = _ := by
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

end SubexponentialSAT.SubexpMainIterationBounds

end OAI.Algorithms
