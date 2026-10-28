import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainParameterBounds

namespace OAI.Algorithms

/-!
# Scheduled bound for the actual node-worker estimate

The measured worker estimate has the form
`Cw * S^3072 * 2^(128*D) * (I+1)^8`. Here `S` bounds the original selected
input words and may already have a subexponential bound. The fixed power
3072 is therefore charged to both the input-polynomial degree and the
exponential constant. The iteration count is the actual layout count.

This module converts that numerical estimate and exposes the exact finite
maximum used by the node collector. It does not assume that stored words
are bounded by their numerical values and does not manufacture a trace.
The input-size/parameter estimates feeding `S` remain available from
`SubexpMainParameterBounds`.
-/

namespace SubexponentialSAT.SubexpMainWorkerScheduleBounds

open Filter SubexpPackingParameters SubexpComputation

/-- Maximum of a finite family's actual iteration counts, including the
empty family. It is used only to describe a uniform collector bound. -/
def maxIterations {Q : ℕ} (counts : Fin Q → ℕ) : ℕ := Finset.univ.sup counts

theorem le_maxIterations {Q : ℕ} (counts : Fin Q → ℕ) (i : Fin Q) :
    counts i ≤ maxIterations counts :=
  Finset.le_sup (Finset.mem_univ i)

theorem maxIterations_le {Q : ℕ} (counts : Fin Q → ℕ) {B : ℝ}
    (hB : 0 ≤ B) (h : ∀ i, (counts i : ℝ) ≤ B) :
    (maxIterations counts : ℝ) ≤ B := by
  unfold maxIterations
  apply Finset.sup_induction (p := fun x : ℕ => (x : ℝ) ≤ B)
  · simpa only [bot_eq_zero, Nat.cast_zero] using hB
  · intro x hx y hy
    change ((max x y : ℕ) : ℝ) ≤ B
    rcases le_total x y with hxy | hyx
    · simpa only [max_eq_right hxy] using hy
    · simpa only [max_eq_left hyx] using hx
  · intro i hi
    exact h i

theorem maxIterations_le_envelope {Q : ℕ} (counts : Fin Q → ℕ) (n : ℕ)
    (h : ∀ i, (counts i : ℝ) ≤ SubexpMainIterationBounds.iterationEnvelope n) :
    (maxIterations counts : ℝ) ≤ SubexpMainIterationBounds.iterationEnvelope n := by
  apply maxIterations_le counts _ h
  unfold SubexpMainIterationBounds.iterationEnvelope
  positivity

/-- Actual enumeration data at every node supplies the maximum bound;
there is no user-supplied estimate for the finite maximum. -/
theorem layout_maxIterations_le {n k Δ : ℕ} [Fact (p n).Prime]
    {E : Type*} [Field E] [Algebra (ZMod (p n)) E]
    {F : Type*} [Fintype F] {P : Factor.Pattern (Fin (D n)) F}
    {c : SubexpLayoutSpec.Parameters (p n) k Δ (r n) (DyadicSchedule.tau n)}
    (layout : SubexpLayoutSpec.Layout (E := E) P c)
    (data : ∀ i : Fin c.Q, SubexpLayoutSpec.EnumerationData layout i) :
    (maxIterations (fun i => (data i).iterationCount) : ℝ) ≤
      SubexpMainIterationBounds.iterationEnvelope n :=
  maxIterations_le_envelope _ n
    (fun i => SubexpMainIterationBounds.enumeration_iteration layout (data i))

/-- Adding one to the iteration count costs a fixed factor `2^j`, even
when the actual iteration count is zero. -/
theorem eventually_shifted_power_bound (j : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    ∀ᶠ n : ℕ in atTop, ∀ I : ℕ,
      (I : ℝ) ≤ SubexpMainIterationBounds.iterationEnvelope n →
      ((I : ℝ) + 1)^j * (2 : ℝ)^(c * (D n : ℝ)) ≤
        (2 : ℝ)^j * (2 : ℝ)^((25 * (j : ℝ) + 66 * c) * scale n) := by
  filter_upwards [eventually_goodInput, SubexpMainIterationBounds.eventually_iterationEnvelope]
    with n hn henv I hI
  have hone : (1 : ℝ) ≤ (2 : ℝ)^(25 * scale n) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg (by norm_num) (scale_nonneg n))
  have hshift : (I : ℝ) + 1 ≤ 2 * (2 : ℝ)^(25 * scale n) := by
    have hi := hI.trans henv
    linarith
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (I : ℝ) + 1) hshift j
  have hdim := mul_le_mul_of_nonneg_left
    (SubexpMainIterationBounds.dimension_le_scale hn) hc
  have hd : (2 : ℝ)^(c * (D n : ℝ)) ≤ (2 : ℝ)^((66 * c) * scale n) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith only [hdim]
  calc
    _ ≤ (2 * (2 : ℝ)^(25 * scale n))^j *
        (2 : ℝ)^((66 * c) * scale n) :=
      mul_le_mul hpow hd (by positivity) (by positivity)
    _ = (2 : ℝ)^j * (2 : ℝ)^((25 * (j : ℝ) + 66 * c) * scale n) := by
      rw [mul_pow, mul_assoc, ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 2
      ring

/-- Explicit conversion of the published node-worker bound. All constants
are fixed before the input length, selected storage size, and node count. -/
theorem eventually_worker_bound (Cw C A : ℝ) (d : ℕ)
    (hCw : 0 ≤ Cw) (_hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, ∀ L S I : ℕ,
      (S : ℝ) ≤ runtimeBound C A d L n →
      (I : ℝ) ≤ SubexpMainIterationBounds.iterationEnvelope n →
      Cw * (S : ℝ)^3072 * (2 : ℝ)^(128 * (D n : ℝ)) * ((I : ℝ) + 1)^8 ≤
        runtimeBound (256 * Cw * C^3072) (3072 * A + 8648) (3072 * d) L n := by
  filter_upwards [eventually_shifted_power_bound 8 128 (by norm_num)]
    with n hi L S I hS hI
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg S) hS 3072
  have he := hi I hI
  norm_num only [show (25 : ℝ) * (8 : ℝ) + 66 * 128 = 8648 by norm_num,
    show (2 : ℝ)^8 = 256 by norm_num] at he
  have hp : (S : ℝ)^3072 * (((I : ℝ) + 1)^8 * (2 : ℝ)^(128 * (D n : ℝ))) ≤
      runtimeBound C A d L n ^3072 * (256 * (2 : ℝ)^(8648 * scale n)) :=
    mul_le_mul hs he (by positivity) (by positivity)
  calc
    _ = Cw * ((S : ℝ)^3072 * (((I : ℝ) + 1)^8 *
        (2 : ℝ)^(128 * (D n : ℝ)))) := by ring
    _ ≤ Cw * (runtimeBound C A d L n ^3072 *
        (256 * (2 : ℝ)^(8648 * scale n))) := mul_le_mul_of_nonneg_left hp hCw
    _ = runtimeBound (256 * Cw * C^3072) (3072 * A + 8648) (3072 * d) L n := by
      rw [runtimeBound_pow]
      unfold runtimeBound
      rw [show d * 3072 = 3072 * d by omega]
      have heq : (2 : ℝ)^((3072 * A) * scale n) * (2 : ℝ)^(8648 * scale n) =
          (2 : ℝ)^((3072 * A + 8648) * scale n) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        ring
      calc
        _ = (256 * Cw * C^3072) * ((L : ℝ) + 1)^(3072 * d) *
            ((2 : ℝ)^((3072 * A) * scale n) * (2 : ℝ)^(8648 * scale n)) := by ring_nf
        _ = _ := by rw [heq]

/-- Apply the same bound directly to the natural-valued measured worker
cost, without treating a counter or a real expression as a trace. -/
theorem eventually_steps_bound (Cw : ℕ) (C A : ℝ) (d : ℕ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, ∀ L S I steps : ℕ,
      steps ≤ Cw * S^3072 * 2^(128 * D n) * (I + 1)^8 →
      (S : ℝ) ≤ runtimeBound C A d L n →
      (I : ℝ) ≤ SubexpMainIterationBounds.iterationEnvelope n →
      (steps : ℝ) ≤
        runtimeBound (256 * Cw * C^3072) (3072 * A + 8648) (3072 * d) L n := by
  filter_upwards [eventually_worker_bound Cw C A d (Nat.cast_nonneg Cw) hC]
    with n hn L S I steps hsteps hS hI
  apply le_trans _ (hn L S I hS hI)
  have hreal := Nat.cast_le (α := ℝ).mpr hsteps
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one,
    ← Real.rpow_natCast, Nat.cast_mul, Nat.cast_ofNat] using hreal

/-- The finite collector may use a maximum instead of separate node
counts. The bound is uniform in the number of nodes and the whole family. -/
theorem eventually_max_worker_bound (Cw C A : ℝ) (d : ℕ)
    (hCw : 0 ≤ Cw) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, ∀ (Q L S : ℕ) (counts : Fin Q → ℕ),
      (S : ℝ) ≤ runtimeBound C A d L n →
      (∀ i, (counts i : ℝ) ≤ SubexpMainIterationBounds.iterationEnvelope n) →
      Cw * (S : ℝ)^3072 * (2 : ℝ)^(128 * (D n : ℝ)) *
          ((maxIterations counts : ℝ) + 1)^8 ≤
        runtimeBound (256 * Cw * C^3072) (3072 * A + 8648) (3072 * d) L n := by
  filter_upwards [eventually_worker_bound Cw C A d hCw hC]
    with n hn Q L S counts hS hcounts
  exact hn L S (maxIterations counts) hS (maxIterations_le_envelope counts n hcounts)

end SubexponentialSAT.SubexpMainWorkerScheduleBounds

end OAI.Algorithms
