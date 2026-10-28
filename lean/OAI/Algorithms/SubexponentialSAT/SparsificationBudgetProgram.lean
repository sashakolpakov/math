import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SparsificationBudget
import OAI.Algorithms.SubexponentialSAT.SubexpParameterProgram
import OAI.Algorithms.SubexponentialSAT.PowerOfTwoLengthProgram

namespace OAI.Algorithms

/-!
# A directly computed dyadic sparsification budget

For each fixed width k, a fixed control constant T suffices.  The selected
parameter is a power of two whose binary length is an affine function of the
binary length of the inverse budget.  This is the explicit witness from
SparsificationBudget.dyadic_witness, rather than the least passing candidate.

The control constant is chosen before the input word.  Program definitions
below manipulate bits only; their specifications use the corresponding
natural-number values.
-/

namespace SubexponentialSAT.SparsificationBudgetProgram

open SubexponentialSAT.SparsificationConstants
open SubexponentialSAT.SparsificationBudget
open SubexponentialSAT.CounterPrograms

/-- A fixed control constant, with the polynomial bound used to certify it. -/
def Control (k T : ℕ) : Prop :=
  ∃ a q : ℕ,
    (∀ M, 2 ≤ M → C M (k - 1) ≤ a * M ^ q) ∧
    1 ≤ T ∧ k ≤ 2 ^ T ∧
    k * (a + 2 + (q + 1) * (T + 2)) ≤ 2 ^ T

theorem exists_control (k : ℕ) : ∃ T, Control k T := by
  obtain ⟨a, q, hC⟩ := C_polynomialBound (k - 1)
  obtain ⟨T, hT, hkT, hc⟩ := exists_controlExponent k a q
  exact ⟨T, a, q, hC, hT, hkT, hc⟩

def dyadicExponent (T s : ℕ) : ℕ := T + 2 * (Nat.log 2 s + 1)

def dyadicM (T s : ℕ) : ℕ := 2 ^ dyadicExponent T s

theorem dyadicM_max_one (T s : ℕ) : dyadicM T (max 1 s) = dyadicM T s := by
  rcases s with _ | s
  · simp [dyadicM, dyadicExponent]
  · rw [max_eq_right (by omega : 1 ≤ s + 1)]

theorem dyadicM_ge_two (T s : ℕ) : 2 ≤ dyadicM T s := by
  have h : 1 ≤ dyadicExponent T s := by unfold dyadicExponent; omega
  simpa [dyadicM] using Nat.pow_le_pow_right (by decide : 0 < 2) h

theorem Control.admissible {k T : ℕ} (h : Control k T)
    (hk : 2 ≤ k) (s : ℕ) (hs : 0 < s) :
    ReciprocalAdmissible k s (dyadicM T s) := by
  obtain ⟨a, q, hC, hT, hkT, hc⟩ := h
  exact (dyadic_witness k a q T s hk hs hC hT hkT hc).1

theorem Control.admissible_normalized {k T : ℕ} (h : Control k T)
    (hk : 2 ≤ k) (s : ℕ) :
    ReciprocalAdmissible k (max 1 s) (dyadicM T s) := by
  simpa only [dyadicM_max_one] using
    h.admissible hk (max 1 s) (by omega)

theorem dyadicM_quadratic_bound (T s : ℕ) (hs : 0 < s) :
    dyadicM T s ≤ (4 * 2 ^ T) * s ^ 2 := by
  have hsup : 2 ^ (Nat.log 2 s + 1) ≤ 2 * s := by
    rw [pow_succ]
    simpa [Nat.mul_comm] using
      Nat.mul_le_mul_right 2 (Nat.pow_log_le_self 2 (by omega : s ≠ 0))
  calc
    dyadicM T s = 2 ^ T * (2 ^ (Nat.log 2 s + 1)) ^ 2 := by
      unfold dyadicM dyadicExponent
      rw [pow_add, ← pow_mul]
      congr 2
      omega
    _ ≤ 2 ^ T * (2 * s) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsup 2)
    _ = (4 * 2 ^ T) * s ^ 2 := by ring

theorem dyadicExponent_le (T s : ℕ) (hs : 0 < s) :
    dyadicExponent T s ≤ T + 2 * s := by
  have h := Nat.succ_le_of_lt (Nat.log_lt_self 2 (by omega : s ≠ 0))
  unfold dyadicExponent
  omega

theorem dyadicM_polynomialBound (T : ℕ) : PolynomialBound (dyadicM T) :=
  ⟨4 * 2 ^ T, 2, fun s hs => dyadicM_quadratic_bound T s (by omega)⟩

theorem dyadicC_polynomialBound (T j : ℕ) :
    PolynomialBound (fun s => C (dyadicM T s) j) :=
  polynomialBound_comp (C_polynomialBound j) (dyadicM_polynomialBound T)
    (fun s _ => dyadicM_ge_two T s)

theorem dyadicL_polynomialBound (T j : ℕ) :
    PolynomialBound (fun s => L (dyadicM T s) j) :=
  polynomialBound_comp (L_polynomialBound j) (dyadicM_polynomialBound T)
    (fun s _ => dyadicM_ge_two T s)

theorem dyadicz_polynomialBound (T d : ℕ) :
    PolynomialBound (fun s => z (dyadicM T s) d) :=
  polynomialBound_comp (z_polynomialBound d) (dyadicM_polynomialBound T)
    (fun s _ => dyadicM_ge_two T s)

theorem dyadicOccurrenceCap_polynomialBound (T k : ℕ) :
    PolynomialBound (fun s => occurrenceCap (dyadicM T s) k) :=
  polynomialBound_comp (f := fun M => occurrenceCap M k) (g := dyadicM T)
    (occurrenceCap_polynomialBound k) (dyadicM_polynomialBound T)
    (fun s _ => dyadicM_ge_two T s)

theorem dyadicThresholdCap_polynomialBound (T k : ℕ) :
    PolynomialBound (fun s => thresholdCap (dyadicM T s) k) :=
  polynomialBound_comp (thresholdCap_polynomialBound k) (dyadicM_polynomialBound T)
    (fun s _ => dyadicM_ge_two T s)

theorem Control.ratio_le {k T : ℕ} (h : Control k T) (hk : 2 ≤ k)
    (s : ℕ) (hs : 0 < s) :
    (k : ℝ) / dyadicM T s ≤ C (dyadicM T s) (k - 1) :=
  (h.admissible hk s hs).ratio_le

theorem Control.logb_budget {k T : ℕ} (h : Control k T) (hk : 2 ≤ k)
    (s : ℕ) (hs : 0 < s) :
    (k : ℝ) / dyadicM T s *
      Real.logb 2 (4 * (C (dyadicM T s) (k - 1) : ℝ) * dyadicM T s / k) ≤
      1 / (s : ℝ) :=
  (h.admissible hk s hs).logb_budget hk hs

/-- The exact binary word produced by the finite program. -/
def outputWord (T s : ℕ) : List Bool :=
  List.replicate (dyadicExponent T s) false ++ [true]

theorem value_zeroes_then_one (e : ℕ) :
    value (List.replicate e false ++ [true]) = 2 ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
      simp only [List.replicate_succ, List.cons_append, value, Bool.toNat_false, zero_add]
      rw [ih, pow_succ]
      omega

theorem outputWord_value (T s : ℕ) : value (outputWord T s) = dyadicM T s :=
  value_zeroes_then_one (dyadicExponent T s)

theorem outputWord_toNat (T s : ℕ) :
    BinaryArithmetic.toNat (outputWord T s) = dyadicM T s := by
  rw [← SubexpParameterProgram.value_eq_toNat]
  exact outputWord_value T s

theorem outputWord_length (T s : ℕ) :
    (outputWord T s).length = dyadicExponent T s + 1 := by
  simp [outputWord]

theorem outputWord_length_eq_size (T s : ℕ) :
    (outputWord T s).length = (dyadicM T s).size := by
  rw [outputWord_length]
  simp [dyadicM, Nat.size_pow]

/-- High zero padding in the input does not affect the selected parameter. -/
theorem outputWord_from_trim (T : ℕ) (xs : List Bool) :
    List.replicate (T + 2 + 2 * (SubexpParameterProgram.trimTail xs.reverse).length)
        false ++ [true] =
      outputWord T (value xs) := by
  rw [SubexpParameterProgram.trimTail_reverse_length, Nat.log2_eq_log_two]
  congr 2
  unfold dyadicExponent
  omega

theorem outputWord_length_le (T : ℕ) (xs : List Bool) :
    (outputWord T (value xs)).length ≤ T + 2 * xs.length + 3 := by
  have hlen := SubexpParameterProgram.trimTail_length_le xs.reverse
  rw [SubexpParameterProgram.trimTail_reverse_length, Nat.log2_eq_log_two,
    List.length_reverse] at hlen
  rw [outputWord_length]
  unfold dyadicExponent
  omega

/-! ## The actual fixed finite program -/

/-- The first stage strips high zero padding and the leading one.  The second
stage writes the fixed T+2 zeroes and two zeroes per remaining input cell. -/
def program (T : ℕ) :=
  ProgramLinking.link SubexpParameterProgram.prepareLogProgram
    (PowerOfTwoLengthProgram.program (T + 2))

@[simp] theorem program_input (T : ℕ) : (program T).inputStack = 0 := rfl

@[simp] theorem program_output (T : ℕ) : (program T).outputStack = 2 := rfl

def runtimeBound (T length : ℕ) : ℕ := T + 10 * length + 17

theorem run_correct (T : ℕ) (xs : List Bool) :
    BitProgram.RunsIn (program T) (runtimeBound T xs.length)
      (BitProgram.initial (program T) xs)
      (BitProgram.terminal (program T) (outputWord T (value xs))) := by
  have h := SubexpParameterProgram.link_io_runs
    SubexpParameterProgram.prepareLogProgram (PowerOfTwoLengthProgram.program (T + 2))
    rfl xs (SubexpParameterProgram.trimTail xs.reverse)
    (List.replicate
      (T + 2 + 2 * (SubexpParameterProgram.trimTail xs.reverse).length) false ++ [true])
    (SubexpParameterProgram.prepareLog_runs xs)
    (PowerOfTwoLengthProgram.run_correct (T + 2)
      (SubexpParameterProgram.trimTail xs.reverse))
  rw [outputWord_from_trim] at h
  apply h.mono
  have hlen := SubexpParameterProgram.trimTail_length_le xs.reverse
  simp only [List.length_reverse] at hlen
  unfold runtimeBound
  omega

theorem call_eval (T : ℕ) (xs : List Bool) :
    ∃ steps ≤ runtimeBound T xs.length,
      StructuredCalls.Eval (.call (program T)) steps
        (StructuredProgram.ioState (0 : Fin 3) xs)
        (StructuredProgram.ioState (2 : Fin 3) (outputWord T (value xs))) := by
  obtain ⟨steps, hsteps, htrace⟩ := run_correct T xs
  exact ⟨steps, hsteps, .call (program T) htrace⟩

theorem primitive_correct (T : ℕ) (xs : List Bool) :
    Computation.RunsIn (BitProgram.primitive (program T)).step
      (BitProgram.primitiveOverhead (program T) * runtimeBound T xs.length)
      ((BitProgram.primitive (program T)).init xs)
      (BitProgram.primitiveCfg (program T)
        (BitProgram.terminal (program T) (outputWord T (value xs)))) := by
  simpa only [BitProgram.primitive_initial] using
    BitProgram.primitive_execution (program T) (run_correct T xs)

theorem runtimeBound_le_linear (T length : ℕ) :
    runtimeBound T length ≤ (T + 17) * (length + 1) := by
  unfold runtimeBound
  nlinarith

/-- The multiplicative constant depends on the fixed control table, before
the unbounded input word is chosen. -/
theorem primitive_linear (T : ℕ) :
    ∃ A : ℕ, 0 < A ∧ ∀ xs : List Bool,
      Computation.RunsIn (BitProgram.primitive (program T)).step (A * (xs.length + 1))
        ((BitProgram.primitive (program T)).init xs)
        (BitProgram.primitiveCfg (program T)
          (BitProgram.terminal (program T) (outputWord T (value xs)))) := by
  refine ⟨BitProgram.primitiveOverhead (program T) * (T + 17),
    Nat.mul_pos (BitProgram.primitiveOverhead_pos _) (by omega), ?_⟩
  intro xs
  apply (primitive_correct T xs).mono
  simpa only [Nat.mul_assoc] using
    Nat.mul_le_mul_left (BitProgram.primitiveOverhead (program T))
      (runtimeBound_le_linear T xs.length)

theorem value_bits (s : ℕ) : value s.bits = s := by
  induction s using Nat.binaryRec' with
  | zero => simp []
  | bit b s hs ih =>
      rw [Nat.bits_append_bit s b hs]
      cases b <;> simp [value, ih, Nat.bit, Nat.add_comm]

theorem bits_length_le (s : ℕ) : s.bits.length ≤ s := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr (Nat.lt_pow_self (by decide))

/-- On canonical binary input, the actual primitive cost is in particular
polynomial in the numerical inverse budget. -/
theorem canonical_primitive_linear (T : ℕ) :
    ∃ A : ℕ, 0 < A ∧ ∀ s : ℕ,
      Computation.RunsIn (BitProgram.primitive (program T)).step (A * (s + 1))
        ((BitProgram.primitive (program T)).init s.bits)
        (BitProgram.primitiveCfg (program T)
          (BitProgram.terminal (program T) (outputWord T s))) := by
  obtain ⟨A, hA, hr⟩ := primitive_linear T
  refine ⟨A, hA, fun s => ?_⟩
  have h := hr s.bits
  rw [value_bits] at h
  exact h.mono (Nat.mul_le_mul_left A (Nat.add_le_add_right (bits_length_le s) 1))

/-- The program works for zero and padded inputs as well.  Zero is normalized
to the harmless reciprocal budget one in the specification only. -/
theorem exists_linear_primitive_selector (k : ℕ) (hk : 2 ≤ k) :
    ∃ T A : ℕ, Control k T ∧ 0 < A ∧ ∀ xs : List Bool,
      value (outputWord T (value xs)) = dyadicM T (value xs) ∧
      ReciprocalAdmissible k (max 1 (value xs)) (dyadicM T (value xs)) ∧
      dyadicM T (value xs) ≤ (4 * 2 ^ T) * (max 1 (value xs)) ^ 2 ∧
      (outputWord T (value xs)).length ≤ T + 2 * xs.length + 3 ∧
      Computation.RunsIn (BitProgram.primitive (program T)).step (A * (xs.length + 1))
        ((BitProgram.primitive (program T)).init xs)
        (BitProgram.primitiveCfg (program T)
          (BitProgram.terminal (program T) (outputWord T (value xs)))) := by
  obtain ⟨T, hT⟩ := exists_control k
  obtain ⟨A, hA, hr⟩ := primitive_linear T
  refine ⟨T, A, hT, hA, fun xs =>
    ⟨outputWord_value T _, hT.admissible_normalized hk _, ?_,
      outputWord_length_le T xs, hr xs⟩⟩
  simpa only [dyadicM_max_one] using
    dyadicM_quadratic_bound T (max 1 (value xs)) (by omega)

/-! ## The input-size to inverse-budget to M pipeline -/

/-- The growing inverse budget s(n) is also computed by a fixed bit program. -/
def fromSizeProgram (T : ℕ) :=
  ProgramLinking.link SubexpParameterProgram.doubleLogProgram (program T)

def fromSizeRuntimeBound (T length : ℕ) : ℕ :=
  2 * SubexpParameterProgram.logBound length + runtimeBound T length

theorem fromSize_correct (T : ℕ) (xs : List Bool) :
    BitProgram.RunsIn (fromSizeProgram T) (fromSizeRuntimeBound T xs.length)
      (BitProgram.initial (fromSizeProgram T) xs)
      (BitProgram.terminal (fromSizeProgram T)
        (outputWord T (SubexpPackingParameters.s (value xs)))) := by
  obtain ⟨middle, hm, hlen, hr⟩ := SubexpParameterProgram.doubleLog_correct xs
  have h := SubexpParameterProgram.link_io_runs
    SubexpParameterProgram.doubleLogProgram (program T) rfl xs middle
    (outputWord T (value middle)) hr (run_correct T middle)
  rw [hm] at h
  apply h.mono
  unfold fromSizeRuntimeBound runtimeBound
  omega

theorem fromSize_call_eval (T : ℕ) (xs : List Bool) :
    ∃ steps ≤ fromSizeRuntimeBound T xs.length,
      StructuredCalls.Eval (.call (fromSizeProgram T)) steps
        (StructuredProgram.ioState (0 : Fin 3) xs)
        (StructuredProgram.ioState (2 : Fin 3)
          (outputWord T (SubexpPackingParameters.s (value xs)))) := by
  obtain ⟨steps, hsteps, htrace⟩ := fromSize_correct T xs
  exact ⟨steps, hsteps, .call (fromSizeProgram T) htrace⟩

theorem fromSizeRuntimeBound_le_quadratic (T length : ℕ) :
    fromSizeRuntimeBound T length ≤ (T + 58) * (length + 1) ^ 2 := by
  unfold fromSizeRuntimeBound runtimeBound
  rw [SubexpParameterProgram.logBound_eq]
  nlinarith

theorem fromSize_primitive (T : ℕ) (xs : List Bool) :
    Computation.RunsIn (BitProgram.primitive (fromSizeProgram T)).step
      (BitProgram.primitiveOverhead (fromSizeProgram T) * fromSizeRuntimeBound T xs.length)
      ((BitProgram.primitive (fromSizeProgram T)).init xs)
      (BitProgram.primitiveCfg (fromSizeProgram T)
        (BitProgram.terminal (fromSizeProgram T)
          (outputWord T (SubexpPackingParameters.s (value xs))))) := by
  simpa only [BitProgram.primitive_initial] using
    BitProgram.primitive_execution (fromSizeProgram T) (fromSize_correct T xs)

theorem fromSize_primitive_quadratic (T : ℕ) :
    ∃ A : ℕ, 0 < A ∧ ∀ xs : List Bool,
      Computation.RunsIn (BitProgram.primitive (fromSizeProgram T)).step
        (A * (xs.length + 1) ^ 2)
        ((BitProgram.primitive (fromSizeProgram T)).init xs)
        (BitProgram.primitiveCfg (fromSizeProgram T)
          (BitProgram.terminal (fromSizeProgram T)
            (outputWord T (SubexpPackingParameters.s (value xs))))) := by
  refine ⟨BitProgram.primitiveOverhead (fromSizeProgram T) * (T + 58),
    Nat.mul_pos (BitProgram.primitiveOverhead_pos _) (by omega), ?_⟩
  intro xs
  apply (fromSize_primitive T xs).mono
  simpa only [Nat.mul_assoc] using
    Nat.mul_le_mul_left (BitProgram.primitiveOverhead (fromSizeProgram T))
      (fromSizeRuntimeBound_le_quadratic T xs.length)

end SubexponentialSAT.SparsificationBudgetProgram

end OAI.Algorithms
