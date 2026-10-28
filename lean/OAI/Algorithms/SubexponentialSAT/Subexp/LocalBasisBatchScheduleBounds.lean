import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchBounds
import OAI.Algorithms.SubexponentialSAT.DyadicParameterBounds
import OAI.Algorithms.SubexponentialSAT.SubexpBlockSizeBounds
import OAI.Algorithms.SubexponentialSAT.SubexpFiniteSearch
import OAI.Algorithms.SubexponentialSAT.BitProgramSpace

namespace OAI.Algorithms

/-!
# The actual local-basis batch at the dyadic schedule

The local size is the number of enumerated universal types plus one. It
bounds the actual scalar words, coefficient list, and serialized native
input bank. Neither the global coordinate count nor the target-ring width
occurs in this size. The previously proved native execution bound, including
any fixed compiler multiplier, is eventually at most `2 ^ scale n`.

The scale comparison uses the higher-power block-size theorem through
`eventually_searchExponent_le_scale`: the polynomial exponent first has
square at most `n`, and then lies below `n / log₂ log₂(n+16)`.
-/

namespace SubexponentialSAT.Subexp.LocalBasisBatchScheduleBounds

open Filter SubexpPackingParameters LocalBasisBatchProgram
open scoped BigOperators

local instance scheduledPrime (n : ℕ) : Fact (p n).Prime := ⟨p_prime n⟩

def localSize (k T n : ℕ) : ℕ := DyadicSchedule.N k T n + 1

theorem block_bounds (k T n : ℕ) (hn : GoodInput n) :
    SubexpBlockSizeBounds.Bounds (DyadicSchedule.N k T n)
      (DyadicSchedule.Q n) (DyadicSchedule.delta k T n)
      (r n) (p n) (DyadicSchedule.R k T n) := by
  exact SubexpBlockSizeBounds.quartic_schedule_bounds (r n) (p n)
    (DyadicSchedule.delta k T n) (DyadicSchedule.R k T n)
    (goodInput_r_ge_two hn) (p_gt_two n).le
    (DyadicParameterBounds.R_le_Q k (DyadicSchedule.delta k T) n)

theorem universal_count (k T n : ℕ) :
    (TypeEnumeration.universalBytes (r n) (DyadicSchedule.Q n)
      (DyadicSchedule.delta k T n)).length = DyadicSchedule.N k T n := by
  rw [TypeEnumeration.universalBytes_length]
  rfl

/-- All numerical premises of the native bound come from the actual schedule.
The extra one accommodates the scalar encoding's leading bit. -/
theorem parameters_le (k T n : ℕ) (hn : GoodInput n) :
    r n ≤ localSize k T n ∧
    DyadicSchedule.Q n ≤ localSize k T n ∧
    DyadicSchedule.delta k T n ≤ localSize k T n ∧
    DyadicSchedule.R k T n ≤ localSize k T n ∧
    p n ≤ localSize k T n ∧
    MatrixWordEncoding.width (p n) ≤ localSize k T n ∧
    (TypeEnumeration.universalBytes (r n) (DyadicSchedule.Q n)
      (DyadicSchedule.delta k T n)).length ≤ localSize k T n := by
  have hb := block_bounds k T n hn
  have hN : DyadicSchedule.N k T n ≤ localSize k T n := Nat.le_succ _
  refine ⟨hb.color_le.trans hN, hb.position_le.trans hN,
    hb.slot_le.trans hN, hb.degree_le.trans hN, hb.prime_le.trans hN, ?_, ?_⟩
  · simpa only [MatrixWordEncoding.width, SubexpLiftRing.baseWidth, one_mul,
      localSize] using Nat.add_le_add_right hb.log_le 1
  · rw [universal_count]
    exact hN

theorem sourceBudget_le (k T n : ℕ) (hn : GoodInput n)
    (hr : 0 < r n) (hQ : 0 < DyadicSchedule.Q n)
    (coefficients alphabet : List (ZMod (p n)))
    (hR : coefficients.length = DyadicSchedule.R k T n)
    (hcard : alphabet.length = p n) :
    sourceBudget (Δ := DyadicSchedule.delta k T n) (p n) hr hQ
      coefficients alphabet ≤ LocalBasisBatchBounds.executionBound (localSize k T n) := by
  obtain ⟨hrU, hQU, hdU, hRU, hpU, hwU, hu⟩ := parameters_le k T n hn
  exact LocalBasisBatchBounds.sourceBudget_le_two_pow (p n) hr hQ
    coefficients alphabet hcard (localSize k T n) hrU hQU hdU
    (hR.le.trans hRU) hpU hwU hu

/-- The extent is the sum of the nine serialized native master words. -/
theorem contextExtent_le (k T n : ℕ) (hn : GoodInput n)
    (coefficients alphabet : List (ZMod (p n)))
    (hR : coefficients.length = DyadicSchedule.R k T n)
    (hcard : alphabet.length = p n) :
    contextExtent (canonicalContext (p n) (r n) (DyadicSchedule.Q n)
      (DyadicSchedule.delta k T n) coefficients alphabet) ≤
        20 * (localSize k T n + 1)^4 := by
  obtain ⟨hrU, hQU, hdU, hRU, hpU, hwU, hu⟩ := parameters_le k T n hn
  exact LocalBasisBatchBounds.contextExtent_le (p n)
    (lt_of_lt_of_le (by decide : 0 < 2) (goodInput_r_ge_two hn))
    (DyadicSchedule.Q_pos n) coefficients alphabet hcard (localSize k T n)
    hrU hQU hdU (hR.le.trans hRU) hpU hwU hu

/-- A bound on the actual total stored bits, including all 128 native stacks.
The fixed factor is deliberately coarse; no input-byte premise is supplied. -/
theorem input_bits_le (k T n : ℕ) (hn : GoodInput n)
    (coefficients alphabet : List (ZMod (p n)))
    (hR : coefficients.length = DyadicSchedule.R k T n)
    (hcard : alphabet.length = p n) (regs : Fin 32 → Bool) :
    BitProgram.stackBits (inputState
      (canonicalContext (p n) (r n) (DyadicSchedule.Q n)
        (DyadicSchedule.delta k T n) coefficients alphabet) regs).stacks ≤
          2560 * (localSize k T n + 1)^4 := by
  have hc := contextExtent_le k T n hn coefficients alphabet hR hcard
  unfold BitProgram.stackBits
  calc
    _ ≤ ∑ _j : Fin 128, 20 * (localSize k T n + 1)^4 := by
      apply Finset.sum_le_sum
      intro j _
      exact (inputState_length_le_contextExtent _ regs j).trans hc
    _ = 2560 * (localSize k T n + 1)^4 := by simp; ring

/-- Each fixed power of the actual universal type count is sublinear
eventually. The incidence hypothesis is discharged from the dyadic choice. -/
theorem block_powers (k T t : ℕ) :
    ∀ᶠ n : ℕ in atTop, DyadicSchedule.N k T n ^ t ≤ n := by
  obtain ⟨C, d, hdelta⟩ := DyadicSchedule.exists_incidence_bound k T
  have hd : ∀ᶠ n : ℕ in atTop,
      DyadicSchedule.delta k T n ≤ C * (s n + 1)^d := by
    filter_upwards [eventually_goodInput] with n hn
    exact hdelta n hn
  exact SubexpParameters.blockSize_subpolynomial C d t (DyadicSchedule.delta k T) hd

/-- Fixed polynomials in the local size fit the stronger target scale,
not just an arbitrary constant multiple of `n`. -/
theorem eventually_polynomial_le_scale (k T C q : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (C : ℝ) * ((localSize k T n : ℝ) + 1)^q ≤ SubexpComputation.scale n := by
  have hreal : SubexpFiniteSearch.SubpolynomialPowers
      (fun n => (DyadicSchedule.N k T n : ℝ)) := by
    intro t _
    filter_upwards [block_powers k T t] with n hn
    exact_mod_cast hn
  filter_upwards [SubexpFiniteSearch.eventually_searchExponent_le_scale
    (fun n => Nat.cast_nonneg (DyadicSchedule.N k T n)) hreal ((C : ℝ) * 2^q) q]
    with n hn
  have hshift : (localSize k T n : ℝ) + 1 ≤
      2 * ((DyadicSchedule.N k T n : ℝ) + 1) := by
    simp only [localSize, Nat.cast_add, Nat.cast_one]
    nlinarith [Nat.cast_nonneg (DyadicSchedule.N k T n) (α := ℝ)]
  calc
    (C : ℝ) * ((localSize k T n : ℝ) + 1)^q ≤
        (C : ℝ) * (2 * ((DyadicSchedule.N k T n : ℝ) + 1))^q :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hshift q) (Nat.cast_nonneg C)
    _ = ((C : ℝ) * 2^q) * ((DyadicSchedule.N k T n : ℝ) + 1)^q := by
      rw [mul_pow]
      ring
    _ ≤ SubexpComputation.scale n := hn

theorem eventually_two_pow_polynomial_le_scale (k T C q : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ((2 ^ (C * (localSize k T n + 1)^q) : ℕ) : ℝ) ≤
        (2 : ℝ) ^ SubexpComputation.scale n := by
  filter_upwards [eventually_polynomial_le_scale k T C q] with n hn
  have he : ((C * (localSize k T n + 1)^q : ℕ) : ℝ) ≤
      SubexpComputation.scale n := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hn
  calc
    ((2 ^ (C * (localSize k T n + 1)^q) : ℕ) : ℝ) =
        (2 : ℝ) ^ ((C * (localSize k T n + 1)^q : ℕ) : ℝ) := by
      simp only [Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ (2 : ℝ) ^ SubexpComputation.scale n :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) he

/-- Fixed compilation overhead is absorbed into the same local polynomial
exponent. It is fixed before the input size varies. -/
theorem mul_executionBound_le (factor U : ℕ) :
    factor * LocalBasisBatchBounds.executionBound U ≤
      2 ^ ((factor + 2000000000000000000000000000) * (U + 1)^10) := by
  have hA : 1 ≤ (U + 1)^10 := Nat.one_le_pow _ _ (by omega)
  unfold LocalBasisBatchBounds.executionBound
  calc
    factor * 2 ^ (2000000000000000000000000000 * (U + 1)^10) ≤
        2^factor * 2 ^ (2000000000000000000000000000 * (U + 1)^10) :=
      Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le
    _ = 2 ^ (factor + 2000000000000000000000000000 * (U + 1)^10) :=
      (pow_add _ _ _).symm
    _ ≤ 2 ^ ((factor + 2000000000000000000000000000) * (U + 1)^10) := by
      apply Nat.pow_le_pow_right (by decide)
      nlinarith only [hA]

/-- This also covers the fixed primitive compiler's actual overhead. -/
theorem eventually_executionBound_le_scale (k T factor : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ((factor * LocalBasisBatchBounds.executionBound (localSize k T n) : ℕ) : ℝ) ≤
        (2 : ℝ) ^ SubexpComputation.scale n := by
  filter_upwards [eventually_two_pow_polynomial_le_scale k T
    (factor + 2000000000000000000000000000) 10] with n hn
  exact (Nat.cast_le.mpr (mul_executionBound_le factor (localSize k T n))).trans hn

/-- Actual native budgets, uniformly over the produced coefficient values
and the chosen complete alphabet order of length `p`. -/
theorem eventually_sourceBudget_le_scale (k T factor : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (hr : 0 < r n) (hQ : 0 < DyadicSchedule.Q n)
      (coefficients alphabet : List (ZMod (p n))),
      coefficients.length = DyadicSchedule.R k T n → alphabet.length = p n →
      ((factor * sourceBudget (Δ := DyadicSchedule.delta k T n)
        (p n) hr hQ coefficients alphabet : ℕ) : ℝ) ≤
          (2 : ℝ) ^ SubexpComputation.scale n := by
  filter_upwards [eventually_goodInput, eventually_executionBound_le_scale k T factor]
    with n hn hb
  intro hr hQ coefficients alphabet hR hcard
  exact (Nat.cast_le.mpr (Nat.mul_le_mul_left factor
    (sourceBudget_le k T n hn hr hQ coefficients alphabet hR hcard))).trans hb

/-- Every physical native input bit is accounted for. The entire fixed bank
is itself eventually bounded by the scale, with no global data in the bound. -/
theorem eventually_input_bits_le_scale (k T : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (coefficients alphabet : List (ZMod (p n))),
      coefficients.length = DyadicSchedule.R k T n → alphabet.length = p n →
      ∀ regs : Fin 32 → Bool,
      (BitProgram.stackBits (inputState
        (canonicalContext (p n) (r n) (DyadicSchedule.Q n)
          (DyadicSchedule.delta k T n) coefficients alphabet) regs).stacks : ℝ) ≤
            SubexpComputation.scale n := by
  filter_upwards [eventually_goodInput, eventually_polynomial_le_scale k T 2560 4]
    with n hn hb
  intro coefficients alphabet hR hcard regs
  have hc := (Nat.cast_le (α := ℝ)).mpr
    (input_bits_le k T n hn coefficients alphabet hR hcard regs)
  exact hc.trans (by simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add,
    Nat.cast_one, Nat.cast_ofNat] using hb)

end SubexponentialSAT.Subexp.LocalBasisBatchScheduleBounds

end OAI.Algorithms
