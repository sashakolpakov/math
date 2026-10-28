import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixPascalProgram

namespace OAI.Algorithms

/-! The coefficient read after the physical adjacent-add passes is exactly
the finite binomial sum in the normalized matrix-entry formula. -/

namespace SubexponentialSAT.Subexp.MatrixPascalProgram

open scoped BigOperators

variable (p : ℕ) [Fact p.Prime]

theorem shift_getD (xs : List (ZMod p)) (j : ℕ) :
    (CoefficientPascalProgram.shiftBy p false xs).getD j 0 =
      xs.getD j 0 + xs.getD (j + 1) 0 := by
  induction xs generalizing j with
  | nil => simp [CoefficientPascalProgram.shiftBy]
  | cons x xs ih =>
      cases j with
      | zero => rfl
      | succ j =>
          change (CoefficientPascalProgram.shiftBy p false xs).getD j 0 =
            xs.getD j 0 + xs.getD (j + 1) 0
          exact ih j

def evaluate (xs : List (ZMod p)) (t : ℕ) : ZMod p :=
  ∑ j ∈ Finset.range xs.length, xs.getD j 0 * (t.choose j : ZMod p)

theorem sum_shift (R t : ℕ) (a : ℕ → ZMod p) (hR : a R = 0) :
    (∑ j ∈ Finset.range R, (a j + a (j + 1)) * (t.choose j : ZMod p)) =
      ∑ j ∈ Finset.range R, a j * ((t + 1).choose j : ZMod p) := by
  cases R with
  | zero => simp
  | succ R =>
      have hsplit :
          (∑ j ∈ Finset.range (R + 1), (a j + a (j + 1)) * (t.choose j : ZMod p)) =
            (∑ j ∈ Finset.range (R + 1), a j * (t.choose j : ZMod p)) +
              ∑ j ∈ Finset.range (R + 1), a (j + 1) * (t.choose j : ZMod p) := by
        simp_rw [add_mul]
        exact Finset.sum_add_distrib
      rw [hsplit]
      rw [Finset.sum_range_succ' (fun j => a j * (t.choose j : ZMod p))]
      rw [Finset.sum_range_succ (fun j => a (j + 1) * (t.choose j : ZMod p))]
      rw [Finset.sum_range_succ' (fun j => a j * ((t + 1).choose j : ZMod p))]
      simp only [hR, zero_mul, add_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
      simp_rw [Nat.choose_succ_succ, Nat.cast_add, mul_add]
      rw [Finset.sum_add_distrib]
      ring

theorem evaluate_shift (xs : List (ZMod p)) (t : ℕ) :
    evaluate p (CoefficientPascalProgram.shiftBy p false xs) t = evaluate p xs (t + 1) := by
  simp only [evaluate, CoefficientPascalProgram.shiftBy_length, shift_getD]
  exact sum_shift p xs.length t (fun j => xs.getD j 0)
    (List.getD_eq_default xs 0 (le_refl _))

theorem evaluate_repeated (xs : List (ZMod p)) (n t : ℕ) :
    evaluate p (repeated p n xs) t = evaluate p xs (n + t) := by
  induction n generalizing xs with
  | zero => simp [repeated]
  | succ n ih =>
      rw [repeated, ih, evaluate_shift]
      congr 1
      omega

@[simp] theorem evaluate_zero (xs : List (ZMod p)) :
    evaluate p xs 0 = xs.getD 0 0 := by
  cases xs with
  | nil => simp [evaluate]
  | cons x xs =>
      rw [evaluate, List.length_cons, Finset.sum_range_succ']
      simp

theorem head_repeated (xs : List (ZMod p)) (n : ℕ) :
    (repeated p n xs).getD 0 0 = evaluate p xs n := by
  simpa using evaluate_repeated p xs n 0

theorem getD_drop (xs : List (ZMod p)) (a j : ℕ) :
    (xs.drop a).getD j 0 = xs.getD (a + j) 0 := by
  induction a generalizing xs with
  | zero => simp
  | succ a ih =>
      cases xs with
      | nil => simp
      | cons x xs =>
          simpa only [List.drop_succ_cons, Nat.succ_add, List.getD_cons_succ] using ih xs

theorem shift_drop (xs : List (ZMod p)) (a : ℕ) :
    (CoefficientPascalProgram.shiftBy p false xs).drop a =
      CoefficientPascalProgram.shiftBy p false (xs.drop a) := by
  induction a generalizing xs with
  | zero => simp
  | succ a ih =>
      cases xs with
      | nil => rfl
      | cons x xs =>
          simpa only [CoefficientPascalProgram.shiftBy, List.drop_succ_cons] using ih xs

theorem repeated_drop (xs : List (ZMod p)) (n a : ℕ) :
    (repeated p n xs).drop a = repeated p n (xs.drop a) := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => rw [repeated, ih, shift_drop, repeated]

/-- This includes out-of-range reads: when `a ≥ xs.length` both sides are zero. -/
theorem repeated_getD (xs : List (ZMod p)) (n a : ℕ) :
    (repeated p n xs).getD a 0 =
      ∑ j ∈ Finset.range (xs.length - a), xs.getD (a + j) 0 * (n.choose j : ZMod p) := by
  have hhead := getD_drop p (repeated p n xs) a 0
  simp only [Nat.add_zero] at hhead
  rw [← hhead, repeated_drop, head_repeated, evaluate, List.length_drop]
  apply Finset.sum_congr rfl
  intro j hj
  rw [getD_drop]

theorem zeroPad_getD (xs : List (ZMod p)) (n j : ℕ) :
    (xs ++ List.replicate n 0).getD j 0 = xs.getD j 0 := by
  induction xs generalizing j with
  | nil => simp [List.getD_eq_getElem?_getD]
  | cons x xs ih =>
      cases j with
      | zero => rfl
      | succ j => simpa using ih j

theorem repeated_getD_congr (n : ℕ) (xs ys : List (ZMod p))
    (h : ∀ j, xs.getD j 0 = ys.getD j 0) :
    ∀ j, (repeated p n xs).getD j 0 = (repeated p n ys).getD j 0 := by
  induction n generalizing xs ys with
  | zero => exact h
  | succ n ih =>
      apply ih
      intro j
      rw [shift_getD, shift_getD, h j, h (j + 1)]

/-- Appending any number of actual zero words does not alter the entry read
after any number of passes. This justifies safe in-range physical selection. -/
theorem repeated_zeroPad_getD (xs : List (ZMod p)) (padding n j : ℕ) :
    (repeated p n (xs ++ List.replicate padding 0)).getD j 0 =
      (repeated p n xs).getD j 0 :=
  repeated_getD_congr p n _ _ (zeroPad_getD p xs padding) j

end SubexponentialSAT.Subexp.MatrixPascalProgram

end OAI.Algorithms
