import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeGeneration

namespace OAI.Algorithms

/-! # A polynomial instruction bound for the fixed four-coordinate node program -/

namespace SubexponentialSAT.SubexpNodeCost

open Subexp.TupleProgram

def payloadSize (xs : List (List Bool)) : ℕ := (xs.map List.length).sum

@[simp] theorem payloadSize_nil : payloadSize [] = 0 := rfl
@[simp] theorem payloadSize_cons (x : List Bool) (xs : List (List Bool)) :
    payloadSize (x :: xs) = x.length + payloadSize xs := rfl
@[simp] theorem payloadSize_append (xs ys : List (List Bool)) :
    payloadSize (xs ++ ys) = payloadSize xs + payloadSize ys := by
  simp [payloadSize]
@[simp] theorem payloadSize_reverse (xs : List (List Bool)) :
    payloadSize xs.reverse = payloadSize xs := by simp [payloadSize]

theorem payloadSize_prefix (word : List Bool) (alphabet : List (List Bool)) :
    payloadSize (alphabet.map (word ++ ·)) =
      alphabet.length * word.length + payloadSize alphabet := by
  induction alphabet with
  | nil => simp
  | cons a as ih => simp [ih, Nat.add_mul]; omega

theorem payloadSize_cartesian (rows alphabet : List (List Bool)) :
    payloadSize (cartesianOutput rows alphabet) =
      alphabet.length * payloadSize rows + rows.length * payloadSize alphabet := by
  rw [cartesianOutput, payloadSize_reverse]
  induction rows with
  | nil => simp
  | cons row rows ih =>
      simp only [List.flatMap_cons, payloadSize_append, payloadSize_prefix,
        ih, payloadSize_cons, List.length_cons]
      ring

theorem budget_affine (xs : List (List Bool)) (a b : ℕ) :
    RecordPrograms.budget (fun x => a * x.length + b) xs =
      (a + 6) * payloadSize xs + (b + 7) * xs.length := by
  induction xs with
  | nil => simp [RecordPrograms.budget]
  | cons x xs ih =>
      simp only [RecordPrograms.budget, ih, payloadSize_cons, List.length_cons]
      ring

theorem tupleCost_eq (alphabet : List (List Bool)) (word : List Bool) :
    tupleCost alphabet word = (12 * alphabet.length + 2) * word.length +
      (25 * payloadSize alphabet + 36 * alphabet.length + 18) := by
  have hb : RecordPrograms.budget (fun x => 5 * x.length + 12 * word.length + 15) alphabet =
      (5 + 6) * payloadSize alphabet + (12 * word.length + 15 + 7) * alphabet.length := by
    simpa only [Nat.add_assoc] using budget_affine alphabet 5 (12 * word.length + 15)
  rw [tupleCost, ProgramEncoding.encodeRecords_length, hb]
  change 7 * (2 * payloadSize alphabet + 2 * alphabet.length + 1) +
    ((5 + 6) * payloadSize alphabet + (12 * word.length + 15 + 7) * alphabet.length) +
      2 * word.length + 11 = _
  ring

theorem expansionCost_eq (rows alphabet : List (List Bool)) :
    expansionCost rows alphabet = 3 + (12 * alphabet.length + 8) * payloadSize rows +
      (25 * payloadSize alphabet + 36 * alphabet.length + 25) * rows.length := by
  have h : tupleCost alphabet = fun word => (12 * alphabet.length + 2) * word.length +
      (25 * payloadSize alphabet + 36 * alphabet.length + 18) := funext (tupleCost_eq alphabet)
  rw [expansionCost, h, budget_affine]
  ring

theorem stepCost_eq (rows alphabet : List (List Bool)) :
    stepCost rows alphabet = 17 + (24 * alphabet.length + 8) * payloadSize rows +
      (37 * payloadSize alphabet + 48 * alphabet.length + 25) * rows.length := by
  rw [stepCost, expansionCost_eq, ProgramEncoding.encodeRecords_length]
  change _ + 6 * (2 * payloadSize (cartesianOutput rows alphabet) +
    2 * (cartesianOutput rows alphabet).length + 1) + 8 = _
  rw [payloadSize_cartesian, cartesianOutput_length]
  ring

theorem powerCost_four (alphabet : List (List Bool)) :
    powerCost alphabet 4 [[]] =
      payloadSize alphabet * (109 * alphabet.length ^ 3 + 109 * alphabet.length ^ 2 +
        77 * alphabet.length + 45) +
      (48 * alphabet.length ^ 4 + 73 * alphabet.length ^ 3 + 73 * alphabet.length ^ 2 +
        73 * alphabet.length + 103) := by
  simp only [powerCost, stepCost_eq, payloadSize_cartesian, cartesianOutput_length,
    payloadSize_cons, payloadSize_nil, List.length_cons, List.length_nil]
  ring

/-- This is the actual composed-program budget, including all four tuple
expansions, nonzero filtering, initialization, and final control transfers. -/
theorem cost_four (alphabet : List (List Bool)) :
    SubexpNodeGeneration.cost alphabet =
      payloadSize alphabet * (213 * alphabet.length ^ 3 + 109 * alphabet.length ^ 2 +
        77 * alphabet.length + 45) +
      (95 * alphabet.length ^ 4 + 73 * alphabet.length ^ 3 + 73 * alphabet.length ^ 2 +
        73 * alphabet.length + 125) := by
  rw [SubexpNodeGeneration.cost, powerCost_four, SubexpNodeFilter.budget, budget_affine]
  simp only [powerRows, payloadSize_cartesian, cartesianOutput_length,
    payloadSize_cons, payloadSize_nil, List.length_cons, List.length_nil]
  ring

theorem payloadSize_le (alphabet : List (List Bool)) (width : ℕ)
    (h : ∀ word ∈ alphabet, word.length ≤ width) :
    payloadSize alphabet ≤ alphabet.length * width := by
  induction alphabet with
  | nil => simp
  | cons word words ih =>
      have hw := h word (by simp)
      have ht := ih (fun x hx => h x (by simp [hx]))
      simp only [payloadSize_cons, List.length_cons, Nat.add_mul, one_mul]
      omega

/-- A uniform polynomial bound; the exponent four comes from the fixed
dimension, not from an unbounded source-level loop parameter. -/
theorem cost_le (alphabet : List (List Bool)) (width : ℕ)
    (h : ∀ word ∈ alphabet, word.length ≤ width) :
    SubexpNodeGeneration.cost alphabet ≤ 1000 * (alphabet.length + 1) ^ 4 * (width + 1) := by
  rw [cost_four]
  have hs := payloadSize_le alphabet width h
  set q := alphabet.length
  calc
    _ ≤ (q * width) * (213 * q ^ 3 + 109 * q ^ 2 + 77 * q + 45) +
        (95 * q ^ 4 + 73 * q ^ 3 + 73 * q ^ 2 + 73 * q + 125) :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ hs) _
    _ ≤ _ + (787 * width * q ^ 4 + 3891 * width * q ^ 3 + 5923 * width * q ^ 2 +
        3955 * width * q + 1000 * width + 905 * q ^ 4 + 3927 * q ^ 3 +
        5927 * q ^ 2 + 3927 * q + 875) := Nat.le_add_right _ _
    _ = _ := by ring

end SubexponentialSAT.SubexpNodeCost

end OAI.Algorithms
