import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.DyadicParameterBounds
import OAI.Algorithms.SubexponentialSAT.SubexpMainIterationBounds

namespace OAI.Algorithms

/-!
# Input and parameter bounds for the actual Main schedule

The parameter record is the implemented dyadic schedule, with fixed `k,T`.
Its polynomial bound is combined with the original input length and the
actual layout iteration bound. The constants precede every varying input,
factor count, and iteration count.

These are numerical estimates. A caller applies them to a separately
proved instruction bound; they do not replace a program trace or a bound
on the lengths of possibly padded stored words.
-/

namespace SubexponentialSAT.SubexpMainParameterBounds

open Filter SubexpPackingParameters SubexpComputation

/-- Every fixed power of the input length plus the actual parameter size
has one input-polynomial bound, uniformly in the leaf's factor count. -/
theorem eventually_input_size_power (k T q : ℕ) :
    ∃ C d : ℕ, 1 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ m L : ℕ,
      n ≤ L → m ≤ DyadicSchedule.delta k T n * D n →
      (L + (DyadicParameterBounds.parameters k T n m).size + 1)^q ≤
        C * (L + 1)^d := by
  obtain ⟨C, d, hC, hsize⟩ := DyadicParameterBounds.eventually_size_polynomial k T
  refine ⟨(C + 1)^q, (d + 1)*q, Nat.one_le_pow _ _ (by omega), ?_⟩
  filter_upwards [hsize] with n hn m L hnL hm
  have hsizeL : (DyadicParameterBounds.parameters k T n m).size ≤
      C * (L + 1)^d :=
    (hn m hm).trans (Nat.mul_le_mul_left C
      (Nat.pow_le_pow_left (Nat.add_le_add_right hnL 1) d))
  have hpow : (L + 1)^d ≤ (L + 1)^(d + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hbase : L + 1 ≤ (L + 1)^(d + 1) := by
    simpa only [pow_one] using
      Nat.pow_le_pow_right (by omega : 1 ≤ L + 1) (by omega : 1 ≤ d + 1)
  have hsum : L + (DyadicParameterBounds.parameters k T n m).size + 1 ≤
      (C + 1) * (L + 1)^(d + 1) := by
    calc
      _ ≤ (L + 1)^(d + 1) + C * (L + 1)^(d + 1) := by
        have hs := hsizeL.trans (Nat.mul_le_mul_left C hpow)
        omega
      _ = _ := by ring
  calc
    _ ≤ ((C + 1) * (L + 1)^(d + 1))^q := Nat.pow_le_pow_left hsum q
    _ = (C + 1)^q * (L + 1)^((d + 1)*q) := by rw [mul_pow, ← pow_mul]

/-- Keep the exact exponent coefficient supplied by the actual iteration
bound. This includes the cases of zero polynomial or iteration powers. -/
theorem eventually_mixed_bound_explicit (k T q j : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    ∃ C d : ℕ, 1 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ m L I : ℕ,
      n ≤ L → m ≤ DyadicSchedule.delta k T n * D n →
      (I : ℝ) ≤ SubexpMainIterationBounds.iterationEnvelope n →
      ((L : ℝ) + (DyadicParameterBounds.parameters k T n m).size + 1)^q *
          (I : ℝ)^j * (2 : ℝ)^(c * (D n : ℝ)) ≤
        runtimeBound C (25 * (j : ℝ) + 66 * c) d L n := by
  obtain ⟨C, d, hC, hsize⟩ := eventually_input_size_power k T q
  refine ⟨C, d, hC, ?_⟩
  filter_upwards [hsize, SubexpMainIterationBounds.eventually_power_bound j c hc]
    with n hs hi m L I hnL hm hI
  have hp : ((L : ℝ) + (DyadicParameterBounds.parameters k T n m).size + 1)^q ≤
      (C : ℝ) * ((L : ℝ) + 1)^d := by
    exact_mod_cast hs m L hnL hm
  have he := hi I hI
  calc
    _ = (((L : ℝ) + (DyadicParameterBounds.parameters k T n m).size + 1)^q) *
        ((I : ℝ)^j * (2 : ℝ)^(c * (D n : ℝ))) := by ring
    _ ≤ ((C : ℝ) * ((L : ℝ) + 1)^d) *
        (2 : ℝ)^((25 * (j : ℝ) + 66 * c) * scale n) :=
      mul_le_mul hp he (by positivity) (by positivity)
    _ = runtimeBound C (25 * (j : ℝ) + 66 * c) d L n := rfl

/-- A positive-constant runtime envelope for fixed powers of the actual
Main parameters and iteration count. All three constants precede `n,m,L,I`. -/
theorem eventually_mixed_bound (k T q j : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    ∃ (C A : ℝ) (d : ℕ), 0 < C ∧ 0 < A ∧
      ∀ᶠ n : ℕ in atTop, ∀ m L I : ℕ,
        n ≤ L → m ≤ DyadicSchedule.delta k T n * D n →
        (I : ℝ) ≤ SubexpMainIterationBounds.iterationEnvelope n →
        ((L : ℝ) + (DyadicParameterBounds.parameters k T n m).size + 1)^q *
            (I : ℝ)^j * (2 : ℝ)^(c * (D n : ℝ)) ≤
          runtimeBound C A d L n := by
  obtain ⟨C, d, hC, hb⟩ := eventually_mixed_bound_explicit k T q j c hc
  refine ⟨C, 25 * (j : ℝ) + 66 * c + 1, d, ?_, by positivity, ?_⟩
  · exact_mod_cast (show 0 < C by omega)
  · filter_upwards [hb] with n hn m L I hnL hm hI
    exact (hn m L I hnL hm hI).trans
      (runtimeBound_mono_exponent (Nat.cast_nonneg C) (by linarith) d L n)

end SubexponentialSAT.SubexpMainParameterBounds

end OAI.Algorithms
