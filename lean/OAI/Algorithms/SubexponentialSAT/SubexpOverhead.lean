import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpScale

namespace OAI.Algorithms

/-!
# Fixed polynomial implementation overhead

These are numerical lemmas for use after an actual implementation simulation
has been proved.  They assign no cost to an arbitrary function or program.
-/

namespace SubexponentialSAT.SubexpComputation

theorem runtimeBound_mono_constant {constant constant' : ℝ}
    (hc : constant ≤ constant') (a : ℝ) (degree inputBits numVars : ℕ) :
    runtimeBound constant a degree inputBits numVars ≤
      runtimeBound constant' a degree inputBits numVars := by
  unfold runtimeBound
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)

theorem input_le_runtimeBound {constant a : ℝ} (hc : 1 ≤ constant)
    (ha : 0 ≤ a) {degree : ℕ} (hd : 0 < degree) (inputBits numVars : ℕ) :
    (inputBits : ℝ) + 1 ≤ runtimeBound constant a degree inputBits numVars := by
  have hbase : (1 : ℝ) ≤ (inputBits : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) inputBits
    linarith
  have hp : (inputBits : ℝ) + 1 ≤ ((inputBits : ℝ) + 1) ^ degree :=
    le_self_pow₀ hbase (Nat.ne_of_gt hd)
  have he : (1 : ℝ) ≤ (2 : ℝ) ^ (a * scale numVars) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg ha (scale_nonneg numVars))
  calc
    (inputBits : ℝ) + 1 ≤ ((inputBits : ℝ) + 1) ^ degree := hp
    _ ≤ constant * ((inputBits : ℝ) + 1) ^ degree :=
      le_mul_of_one_le_left (by positivity) hc
    _ ≤ runtimeBound constant a degree inputBits numVars :=
      le_mul_of_one_le_right (by positivity) he

/-- A measured source time plus sequential input handling fits twice its
envelope.  Taking a fixed power multiplies only fixed exponent constants. -/
theorem polynomial_overhead_le {constant a factor sourceTime : ℝ}
    (hc : 1 ≤ constant) (ha : 0 ≤ a) (hf : 0 ≤ factor)
    (ht : 0 ≤ sourceTime) {degree : ℕ} (hd : 0 < degree)
    (inputBits numVars power : ℕ)
    (hsource : sourceTime ≤ runtimeBound constant a degree inputBits numVars) :
    factor * (sourceTime + (inputBits : ℝ) + 1) ^ power ≤
      runtimeBound (factor * (2 * constant) ^ power) ((power : ℝ) * a)
        (degree * power) inputBits numVars := by
  have hin := input_le_runtimeBound hc ha hd inputBits numVars
  have hsum : sourceTime + (inputBits : ℝ) + 1 ≤
      runtimeBound (2 * constant) a degree inputBits numVars := by
    rw [runtimeBound_mul_constant]
    linarith
  calc
    factor * (sourceTime + (inputBits : ℝ) + 1) ^ power ≤
        factor * runtimeBound (2 * constant) a degree inputBits numVars ^ power :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsum power) hf
    _ = runtimeBound (factor * (2 * constant) ^ power) ((power : ℝ) * a)
        (degree * power) inputBits numVars := by
      rw [runtimeBound_pow, runtimeBound_mul_constant]

/-- The natural-number operation counts used by machine simulations have
exactly the same absorption property; no real-to-integer rounding is hidden. -/
theorem nat_polynomial_overhead_le {constant a : ℝ}
    (hc : 1 ≤ constant) (ha : 0 ≤ a) {degree : ℕ} (hd : 0 < degree)
    (inputBits numVars power factor sourceTime targetTime : ℕ)
    (hsource : (sourceTime : ℝ) ≤ runtimeBound constant a degree inputBits numVars)
    (htarget : targetTime ≤ factor * (sourceTime + inputBits + 1) ^ power) :
    (targetTime : ℝ) ≤
      runtimeBound ((factor : ℝ) * (2 * constant) ^ power) ((power : ℝ) * a)
        (degree * power) inputBits numVars := by
  have hcast : (targetTime : ℝ) ≤
      (factor : ℝ) * ((sourceTime : ℝ) + (inputBits : ℝ) + 1) ^ power := by
    exact_mod_cast htarget
  exact hcast.trans (polynomial_overhead_le hc ha (Nat.cast_nonneg factor)
    (Nat.cast_nonneg sourceTime) hd inputBits numVars power hsource)

/-- A polynomial-size normalization and deletion of unused variables preserve
the bound.  This accounts for the actual output size of a preprocessor; its
execution still has to be charged separately. -/
theorem polynomial_input_overhead_le {constant a sizeConstant : ℝ}
    (hc : 0 ≤ constant) (ha : 0 ≤ a) (hs : 0 ≤ sizeConstant)
    (degree sizeDegree inputBits outputBits originalVars normalizedVars : ℕ)
    (hsize : (outputBits : ℝ) + 1 ≤
      sizeConstant * ((inputBits : ℝ) + 1) ^ sizeDegree)
    (hvars : normalizedVars ≤ originalVars) :
    runtimeBound constant a degree outputBits normalizedVars ≤
      runtimeBound (constant * sizeConstant ^ degree) a (sizeDegree * degree)
        inputBits originalVars := by
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (outputBits : ℝ) + 1)
    hsize degree
  have hexp : (2 : ℝ) ^ (a * scale normalizedVars) ≤
      (2 : ℝ) ^ (a * scale originalVars) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_left (scale_monotone hvars) ha)
  unfold runtimeBound
  calc
    constant * ((outputBits : ℝ) + 1) ^ degree *
        (2 : ℝ) ^ (a * scale normalizedVars) ≤
      constant * (sizeConstant * ((inputBits : ℝ) + 1) ^ sizeDegree) ^ degree *
        (2 : ℝ) ^ (a * scale originalVars) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpow hc) hexp (by positivity) (by positivity)
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

end SubexponentialSAT.SubexpComputation

end OAI.Algorithms
