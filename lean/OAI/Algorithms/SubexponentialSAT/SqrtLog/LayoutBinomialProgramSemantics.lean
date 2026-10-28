import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgramMath

namespace OAI.Algorithms

/-! The physical Pascal scan computes the exact binomial row, in increasing
column order, including columns above the row index. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

open SubexponentialSAT.BinaryArithmetic

def natScan (prior : ℕ) : List ℕ → List ℕ
  | [] => []
  | old :: rest => (prior + old) :: natScan old rest

def scanPrior (h : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => h.choose k

theorem scan_cell (h k : ℕ) :
    scanPrior h k + h.choose k = (h+1).choose k := by
  cases k with
  | zero => simp [scanPrior]
  | succ k => simp [scanPrior, Nat.choose_succ_succ]

theorem natScan_choose_offset (h R k : ℕ) :
    natScan (scanPrior h k) ((List.range R).map (fun j => h.choose (k+j))) =
      (List.range R).map (fun j => (h+1).choose (k+j)) := by
  induction R generalizing k with
  | zero => rfl
  | succ R ih =>
    rw [List.range_succ_eq_map]
    simp only [List.map_cons,List.map_map,Nat.add_zero,
      natScan,scan_cell]
    congr 1
    simpa [scanPrior, Function.comp_def, Nat.succ_eq_add_one, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using ih (k+1)

theorem natScan_choose (h R : ℕ) :
    natScan 0 ((List.range R).map (h.choose)) =
      (List.range R).map ((h+1).choose) := by
  simpa only [scanPrior,Nat.zero_add] using natScan_choose_offset h R 0

theorem scan_values (prior : List Bool) (xs : List (List Bool)) :
    (scan prior xs).map BinaryArithmetic.toNat = natScan (BinaryArithmetic.toNat prior) (xs.map BinaryArithmetic.toNat) := by
  induction xs generalizing prior with
  | nil => rfl
  | cons x xs ih => simp only [scan,List.map_cons,natScan,ih,toNat_add]

theorem iterate_values (n h R : ℕ) (xs : List (List Bool))
    (hx : xs.map BinaryArithmetic.toNat = (List.range R).map h.choose) :
    (iterate n xs).map BinaryArithmetic.toNat = (List.range R).map (h+n).choose := by
  induction n generalizing h xs with
  | zero => simpa [iterate] using hx
  | succ n ih =>
    have hs : (scan [] xs).map BinaryArithmetic.toNat = (List.range R).map (h+1).choose := by
      rw [scan_values,hx]
      exact natScan_choose h R
    simpa [iterate,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (h+1) _ hs

@[simp] theorem initial_zero : initial 0 = [] := by simp [initial]

@[simp] theorem initial_succ (R : ℕ) :
    initial (R+1) = [true] :: List.replicate R [] := by
  simp [initial,List.ofFn_succ]

theorem initial_values (R : ℕ) :
    (initial R).map BinaryArithmetic.toNat = (List.range R).map (Nat.choose 0) := by
  cases R with
  | zero => simp
  | succ R =>
    simp [initial_succ,List.range_succ_eq_map,List.map_map,Function.comp_def,bitVal]

theorem iterate_initial_values (h R : ℕ) :
    (iterate h (initial R)).map BinaryArithmetic.toNat = (List.range R).map h.choose := by
  simpa using iterate_values h 0 R (initial R) (initial_values R)

theorem iterate_initial_word_length (h R : ℕ) :
    ∀ x ∈ iterate h (initial R), x.length ≤ h+1 := by
  simpa [Nat.add_comm] using iterate_word_length h (initial R) 1 (initial_word_length R)

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

end OAI.Algorithms
