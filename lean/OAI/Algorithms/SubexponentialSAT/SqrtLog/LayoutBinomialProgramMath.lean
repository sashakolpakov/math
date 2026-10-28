import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.BinaryArithmetic

namespace OAI.Algorithms

/-! Pascal's recurrence on actual little-endian words. The old row, rather
than the growing new row, supplies the carry at each position. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

open SubexponentialSAT.BinaryArithmetic

def scan : List Bool → List (List Bool) → List (List Bool)
  | _, [] => []
  | prior, old :: rest => add prior old :: scan old rest

def last : List Bool → List (List Bool) → List Bool
  | prior, [] => prior
  | _, old :: rest => last old rest

@[simp] theorem scan_length (prior : List Bool) (xs : List (List Bool)) :
    (scan prior xs).length = xs.length := by
  induction xs generalizing prior with
  | nil => rfl
  | cons x xs ih => simp [scan, ih]

theorem scan_word_length (prior : List Bool) (xs : List (List Bool))
    (B : ℕ) (hp : prior.length ≤ B) (hx : ∀ x ∈ xs, x.length ≤ B) :
    ∀ x ∈ scan prior xs, x.length ≤ B + 1 := by
  induction xs generalizing prior with
  | nil => simp [scan]
  | cons old rest ih =>
    have ho := hx old (by simp)
    intro x h
    simp only [scan, List.mem_cons] at h
    rcases h with rfl | h
    · exact (length_add prior old).trans (by omega)
    · exact ih old ho (fun y hy => hx y (by simp [hy])) x h

theorem last_length (prior : List Bool) (xs : List (List Bool))
    (B : ℕ) (hp : prior.length ≤ B) (hx : ∀ x ∈ xs, x.length ≤ B) :
    (last prior xs).length ≤ B := by
  induction xs generalizing prior with
  | nil => exact hp
  | cons old rest ih => exact ih old (hx old (by simp)) (fun y hy => hx y (by simp [hy]))

def iterate : ℕ → List (List Bool) → List (List Bool)
  | 0, xs => xs
  | h + 1, xs => iterate h (scan [] xs)

@[simp] theorem iterate_length (h : ℕ) (xs : List (List Bool)) :
    (iterate h xs).length = xs.length := by
  induction h generalizing xs with
  | zero => rfl
  | succ h ih => simp [iterate, ih]

theorem iterate_word_length (h : ℕ) (xs : List (List Bool)) (B : ℕ)
    (hx : ∀ x ∈ xs, x.length ≤ B) :
    ∀ x ∈ iterate h xs, x.length ≤ B + h := by
  induction h generalizing xs B with
  | zero => simpa [iterate] using hx
  | succ h ih =>
    have ht := ih (scan [] xs) (B+1) (scan_word_length [] xs B (by simp) hx)
    simpa [iterate, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht

def initial (R : ℕ) : List (List Bool) :=
  List.ofFn fun i : Fin R => if i.val = 0 then [true] else []

@[simp] theorem initial_length (R : ℕ) : (initial R).length = R := by simp [initial]

theorem initial_word_length (R : ℕ) : ∀ x ∈ initial R, x.length ≤ 1 := by
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  split <;> simp

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

end OAI.Algorithms
