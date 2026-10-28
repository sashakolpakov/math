import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.DyadicCallbackWordBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.AsymptoticTarget

namespace OAI.Algorithms

/-! Stored-word and callback costs for the square-root-logarithmic schedule.
The ambient dimension is always the original `n`; arithmetic padding in the
threshold bank is bounded by the actual producer's length theorem. -/

namespace SubexponentialSAT.SqrtLog.SparsifyProgram

open CandidatePrepareProgram ExecSunflowerCallbackBounds
open DyadicMaskedSearchBounds DyadicCallbackInputs
open Asymptotic

def threshold (k T n : ℕ) : ℕ :=
  SparsificationBudget.thresholdCap (SparsificationBudgetProgram.dyadicM T (s n)) k

def arity (T n j : ℕ) : ℕ :=
  SparsificationConstants.z (SparsificationBudgetProgram.dyadicM T (s n)) j

theorem arity_le_threshold (k T n j : ℕ) (hj : j ≤ k) :
    arity T n j ≤ threshold k T n :=
  SparsificationBudget.z_le_thresholdCap _ _ _ hj

def thresholdCoefficient (k T : ℕ) : ℕ :=
  SparsificationThresholdTable.widthCoeff (SparsificationThresholdTable.expressions k) * (18 * (T + 4))

theorem selector_output_length_le (T n : ℕ) :
    (SparsificationBudgetProgram.outputWord T (s n)).length + 1 ≤ (18 * (T + 4)) * (n + 1) := by
  have h := SparsificationBudgetProgram.outputWord_length_le T (s n).bits
  rw [SparsificationBudgetProgram.value_bits] at h
  have hb := SparsificationBudgetProgram.bits_length_le (s n)
  have hs := Asymptotic.s_le_L n
  have hlog := Nat.log2_le_self (n + 16)
  dsimp [Asymptotic.L] at hs
  nlinarith

theorem threshold_coefficient_le (k : ℕ) (i : Fin (k - 1)) :
    ArithmeticExpressionProgram.widthCoeff
      (SparsificationThresholdProgram.thresholdExpr (i.val + 2)) ≤
        SparsificationThresholdTable.widthCoeff (SparsificationThresholdTable.expressions k) := by
  exact Finset.single_le_sum (fun j _ => Nat.zero_le
    (ArithmeticExpressionProgram.widthCoeff (SparsificationThresholdTable.expressions k j)))
    (Finset.mem_univ i)

/-- This applies to the exact padded words returned by the arithmetic table;
it does not replace those words by a canonical representation. -/
theorem threshold_word_length_le (k T n m r : ℕ) (i : Fin (k - 1))
    (word : List Bool)
    (hword : word.length ≤ ArithmeticExpressionProgram.widthCoeff
      (SparsificationThresholdProgram.thresholdExpr (i.val + 2)) *
        ((SparsificationBudgetProgram.outputWord T (s n)).length + 1)) :
    word.length ≤ thresholdCoefficient k T * localSize n m r k := by
  have hlocal : n + 1 ≤ localSize n m r k := by unfold localSize; omega
  calc
    word.length ≤ ArithmeticExpressionProgram.widthCoeff
      (SparsificationThresholdProgram.thresholdExpr (i.val + 2)) *
        ((SparsificationBudgetProgram.outputWord T (s n)).length + 1) := hword
    _ ≤ SparsificationThresholdTable.widthCoeff (SparsificationThresholdTable.expressions k) *
        ((18 * (T + 4)) * (n + 1)) := Nat.mul_le_mul (threshold_coefficient_le k i)
          (selector_output_length_le T n)
    _ ≤ thresholdCoefficient k T * localSize n m r k := by
      simpa only [thresholdCoefficient, Nat.mul_assoc] using
        Nat.mul_le_mul_left (thresholdCoefficient k T) hlocal

theorem aggregate_executed_threshold_le (F : Formula) (n m r k T : ℕ)
    (i : Fin (k - 1)) (limit threshold : List Bool)
    (hcount : F.length ≤ m) (hwidth : ∀ C ∈ F, C.length ≤ k)
    (hliteral : ∀ C ∈ F, ∀ bits ∈ C, bits.length ≤ 2 * n + 1)
    (hlimit : limit.length ≤ m + 1)
    (hthreshold : threshold.length ≤ ArithmeticExpressionProgram.widthCoeff
      (SparsificationThresholdProgram.thresholdExpr (i.val + 2)) *
        ((SparsificationBudgetProgram.outputWord T (s n)).length + 1)) :
    aggregate F k r (DyadicWidth.width m) limit (i.val + 2).bits threshold ≤
      (thresholdCoefficient k T + 24) * localSize n m r k ^ 3 := by
  have hi : i.val + 2 ≤ k := by have := i.isLt; omega
  exact aggregate_threshold_le F n m r k (DyadicWidth.width m) (thresholdCoefficient k T)
    limit (i.val + 2).bits threshold hcount hwidth hliteral (DyadicWidth.width_le_succ m)
    hlimit ((SparsificationBudgetProgram.bits_length_le _).trans (by omega))
    (threshold_word_length_le k T n m r i threshold hthreshold)

def callbackCoefficient (k T : ℕ) : ℕ := 3000000 * (thresholdCoefficient k T + 24) ^ 8

theorem callback_envelope_le (F : Formula) (n m r k T : ℕ)
    (i : Fin (k - 1)) (limit threshold : List Bool)
    (hcount : F.length ≤ m) (hwidth : ∀ C ∈ F, C.length ≤ k)
    (hliteral : ∀ C ∈ F, ∀ bits ∈ C, bits.length ≤ 2 * n + 1)
    (hlimit : limit.length ≤ m + 1)
    (hthreshold : threshold.length ≤ ArithmeticExpressionProgram.widthCoeff
      (SparsificationThresholdProgram.thresholdExpr (i.val + 2)) *
        ((SparsificationBudgetProgram.outputWord T (s n)).length + 1)) :
    3000000 * (aggregate F k r (DyadicWidth.width m) limit (i.val + 2).bits threshold) ^ 8 ≤
      callbackCoefficient k T * localSize n m r k ^ 24 := by
  calc
    _ ≤ 3000000 * ((thresholdCoefficient k T + 24) * localSize n m r k ^ 3) ^ 8 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
        (aggregate_executed_threshold_le F n m r k T i limit threshold
          hcount hwidth hliteral hlimit hthreshold) 8)
    _ = _ := by simp only [callbackCoefficient, mul_pow, ← pow_mul]; ring

end SubexponentialSAT.SqrtLog.SparsifyProgram

end OAI.Algorithms
