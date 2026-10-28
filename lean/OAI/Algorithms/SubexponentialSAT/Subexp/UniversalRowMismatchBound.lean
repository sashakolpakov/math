import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowMismatchTypes

namespace OAI.Algorithms

/-! Bounds for the actual unary-range, mismatch-filter and type-extractor
programs used by the universal-row constructor. -/

namespace SubexponentialSAT.Subexp.UniversalRowMismatchBound

open MulticolorTypes
open MismatchPlanProgram (indexRecords callbackCost sourceBound)

def mismatchBound (S : ℕ) : ℕ := 400 * S ^ 3
def extractBound (S : ℕ) : ℕ := 700 * S ^ 3
def commandBound (S : ℕ) : ℕ := 1200 * S ^ 3

theorem monotone_mismatchBound : Monotone mismatchBound := by
  intro S T h
  exact Nat.mul_le_mul_left 400 (Nat.pow_le_pow_left h 3)

theorem monotone_extractBound : Monotone extractBound := by
  intro S T h
  exact Nat.mul_le_mul_left 700 (Nat.pow_le_pow_left h 3)

theorem monotone_commandBound : Monotone commandBound := by
  intro S T h
  exact Nat.mul_le_mul_left 1200 (Nat.pow_le_pow_left h 3)

theorem indexRecords_budget (width : ℕ) (positions : List ℕ) :
    RecordPrograms.budget (callbackCost width) (indexRecords positions) =
      (28 * width + 45) * positions.sum + (43 * width + 87) * positions.length := by
  induction positions with
  | nil => simp [indexRecords, RecordPrograms.budget]
  | cons i positions ih =>
      simp only [indexRecords, List.map_cons, RecordPrograms.budget, callbackCost,
        List.length_replicate, List.sum_cons, List.length_cons] at ih ⊢
      rw [ih]
      ring

theorem indexRecords_encoded_length (positions : List ℕ) :
    (ProgramEncoding.encodeRecords (indexRecords positions)).length =
      2 * positions.sum + 2 * positions.length + 1 := by
  simpa [indexRecords, List.map_map, Function.comp_def] using
    ProgramEncoding.encodeRecords_length (indexRecords positions)

theorem sourceBound_indexRecords (width : ℕ) (positions : List ℕ) :
    sourceBound width (indexRecords positions) =
      (28 * width + 65) * positions.sum + (43 * width + 107) * positions.length + 18 := by
  change 8 + RecordPrograms.budget (callbackCost width) (indexRecords positions) +
    10 * (ProgramEncoding.encodeRecords (indexRecords positions)).length = _
  rw [indexRecords_budget, indexRecords_encoded_length]
  ring

theorem sum_range_le_sq (Q : ℕ) : (List.range Q).sum ≤ Q ^ 2 := by
  induction Q with
  | zero => simp
  | succ Q ih =>
      rw [List.range_succ, List.sum_append, List.sum_singleton]
      nlinarith

theorem budget_le_polynomial (Q r : ℕ) :
    UniversalRowMismatchProgram.budget Q r ≤
      (28 * r + 77) * Q ^ 2 + (43 * r + 139) * Q + 32 := by
  have hrange := SubexpUnaryRangeProgram.steps_le 0 Q
  have hsum := Nat.mul_le_mul_left (28 * r + 65) (sum_range_le_sq Q)
  unfold UniversalRowMismatchProgram.budget
  rw [sourceBound_indexRecords]
  simp only [List.sum_reverse, List.length_reverse, List.length_range]
  simp only [Nat.zero_add] at hrange
  nlinarith only [hrange, hsum]

theorem budget_le (Q r S : ℕ) (hS : 1 ≤ S) (hQ : Q ≤ S) (hr : r ≤ S) :
    UniversalRowMismatchProgram.budget Q r ≤ mismatchBound S := by
  have h12 : S ≤ S ^ 2 := by nlinarith
  have h23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  apply (budget_le_polynomial Q r).trans
  change _ ≤ 400 * S ^ 3
  calc
    _ ≤ (28 * S + 77) * S ^ 2 + (43 * S + 139) * S + 32 := by gcongr
    _ ≤ _ := by nlinarith only [hS, h12, h23]

variable {r Q Δ : ℕ}

theorem extractBudget_le (i : Fin Δ) (S : ℕ) (hS : 1 ≤ S)
    (hQ : Q ≤ S) (hr : r ≤ S) (hΔ : Δ ≤ S)
    (htype : CollisionProgram.typeWidth r Q Δ ≤ S) :
    UniversalRowMismatchTypes.extractBudget (r := r) (Q := Q) i ≤ extractBound S := by
  have hi : i.val + 1 ≤ S := by have := i.isLt; omega
  have hQr : Q * r ≤ S ^ 2 := by simpa only [pow_two] using Nat.mul_le_mul hQ hr
  have h12 : S ≤ S ^ 2 := by nlinarith
  have h23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  unfold UniversalRowMismatchTypes.extractBudget extractBound
  calc
    _ ≤ 36 * S + 4 * S * (14 * S ^ 2 + 17) + 203 * S ^ 2 + 265 := by gcongr
    _ ≤ _ := by nlinarith only [hS, h12, h23]

theorem commandCost_le (i : Fin Δ) (S : ℕ) (hS : 1 ≤ S)
    (hQ : Q ≤ S) (hr : r ≤ S) (hΔ : Δ ≤ S)
    (htype : CollisionProgram.typeWidth r Q Δ ≤ S) :
    UniversalRowMismatchTypes.extractBudget (r := r) (Q := Q) i +
      UniversalRowMismatchProgram.budget Q r + 8 * (Q * r) + 12 ≤ commandBound S := by
  have he := extractBudget_le i S hS hQ hr hΔ htype
  have hm := budget_le Q r S hS hQ hr
  have hQr : Q * r ≤ S ^ 2 := by simpa only [pow_two] using Nat.mul_le_mul hQ hr
  have h12 : S ≤ S ^ 2 := by nlinarith
  have h23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  unfold extractBound at he
  unfold mismatchBound at hm
  unfold commandBound
  nlinarith only [he, hm, hQr, hS, h12, h23]

end SubexponentialSAT.Subexp.UniversalRowMismatchBound

end OAI.Algorithms
