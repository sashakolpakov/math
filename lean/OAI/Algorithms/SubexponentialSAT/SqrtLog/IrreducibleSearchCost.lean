import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch

namespace OAI.Algorithms

/-!
# Counted scalar implementation of the irreducible-polynomial search

The traces below execute the finite arithmetic and Boolean tests and count
their scalar operations. This is a scalar trace, not a claim that arbitrary
natural-number indexing or list construction costs one primitive bit step.
All stored scalar coefficients are in the fixed field F₃.
-/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearch

open scoped BigOperators

def convolutionTrace {d : ℕ} (a b : Fin d → F) (j : ℕ) : ℕ → F × ℕ
  | 0 => (0, 0)
  | n + 1 =>
      let rest := convolutionTrace a b j n
      (rest.1 + entry a n * entry b (j - n), rest.2 + 2)

theorem convolutionTrace_value {d : ℕ} (a b : Fin d → F) (j n : ℕ) :
    (convolutionTrace a b j n).1 =
      ∑ i ∈ Finset.range n, entry a i * entry b (j - i) := by
  induction n with
  | zero => simp [convolutionTrace]
  | succ n ih => simp [convolutionTrace, ih, Finset.sum_range_succ]

@[simp] theorem convolutionTrace_count {d : ℕ} (a b : Fin d → F) (j n : ℕ) :
    (convolutionTrace a b j n).2 = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [convolutionTrace, ih, Nat.mul_add]

def boolTrace {A : Type*} (combine : Bool → Bool → Bool) (initial : Bool)
    (evaluate : A → Bool × ℕ) : List A → Bool × ℕ
  | [] => (initial, 0)
  | a :: as =>
      let current := evaluate a
      let rest := boolTrace combine initial evaluate as
      (combine current.1 rest.1, current.2 + rest.2 + 1)

theorem boolTrace_all_value {A : Type*} (evaluate : A → Bool × ℕ) (as : List A) :
    (boolTrace (· && ·) true evaluate as).1 = as.all (fun a => (evaluate a).1) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [boolTrace, ih]

theorem boolTrace_any_value {A : Type*} (evaluate : A → Bool × ℕ) (as : List A) :
    (boolTrace (· || ·) false evaluate as).1 = as.any (fun a => (evaluate a).1) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [boolTrace, ih]

theorem boolTrace_count_le {A : Type*} (combine : Bool → Bool → Bool) (initial : Bool)
    (evaluate : A → Bool × ℕ) (as : List A) (bound : ℕ)
    (h : ∀ a ∈ as, (evaluate a).2 ≤ bound) :
    (boolTrace combine initial evaluate as).2 ≤ as.length * (bound + 1) := by
  induction as with
  | nil => simp [boolTrace]
  | cons a as ih =>
      have ha := h a List.mem_cons_self
      have ht := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
      simp only [boolTrace, List.length_cons]
      nlinarith

def nonconstantTrace {n : ℕ} (a : Fin n → F) : Bool × ℕ :=
  boolTrace (· || ·) false (fun i => (decide (0 < i.val ∧ a i ≠ 0), 2)) (List.finRange n)

@[simp] theorem nonconstantTrace_value {n : ℕ} (a : Fin n → F) :
    (nonconstantTrace a).1 = nonconstant a := by
  simp only [nonconstantTrace, boolTrace_any_value, nonconstant]

theorem nonconstantTrace_count {n : ℕ} (a : Fin n → F) :
    (nonconstantTrace a).2 ≤ 3 * n := by
  simpa [nonconstantTrace, Nat.mul_comm] using
    boolTrace_count_le (· || ·) false
      (fun i : Fin n => (decide (0 < i.val ∧ a i ≠ 0), 2)) (List.finRange n) 2
      (fun _ _ => Nat.le_refl _)

def coefficientTrace {d : ℕ} (c : Fin d → F) (a b : Fin (d + 1) → F) (j : ℕ) :
    Bool × ℕ :=
  let conv := convolutionTrace a b j (j + 1)
  (decide (conv.1 = candidateEntry c j), conv.2 + 2)

@[simp] theorem coefficientTrace_value {d : ℕ} (c : Fin d → F)
    (a b : Fin (d + 1) → F) (j : ℕ) :
    (coefficientTrace c a b j).1 = decide (convolution a b j = candidateEntry c j) := by
  simp only [coefficientTrace, convolutionTrace_value, convolution]
  rfl

def productTrace {d : ℕ} (c : Fin d → F) (a b : Fin (d + 1) → F) : Bool × ℕ :=
  boolTrace (· && ·) true (coefficientTrace c a b) (List.range (2 * d + 1))

@[simp] theorem productTrace_value {d : ℕ} (c : Fin d → F)
    (a b : Fin (d + 1) → F) : (productTrace c a b).1 = productEq c a b := by
  simp only [productTrace, boolTrace_all_value, coefficientTrace_value, productEq]

theorem productTrace_count {d : ℕ} (c : Fin d → F) (a b : Fin (d + 1) → F) :
    (productTrace c a b).2 ≤ (2 * d + 1) * (4 * d + 5) := by
  apply (boolTrace_count_le (· && ·) true (coefficientTrace c a b)
    (List.range (2 * d + 1)) (4 * d + 4) ?_).trans_eq
      (by simp)
  intro j hj
  have hj' : j < 2 * d + 1 := List.mem_range.mp hj
  simp only [coefficientTrace, convolutionTrace_count]
  omega

def pairTrace {d : ℕ} (c : Fin d → F)
    (ab : (Fin (d + 1) → F) × (Fin (d + 1) → F)) : Bool × ℕ :=
  let left := nonconstantTrace ab.1
  let right := nonconstantTrace ab.2
  let product := productTrace c ab.1 ab.2
  (!(left.1 && right.1 && product.1), left.2 + right.2 + product.2 + 3)

@[simp] theorem pairTrace_value {d : ℕ} (c : Fin d → F)
    (ab : (Fin (d + 1) → F) × (Fin (d + 1) → F)) :
    (pairTrace c ab).1 = pairPass c ab := by
  simp only [pairTrace, nonconstantTrace_value, productTrace_value, pairPass]

theorem pairTrace_count {d : ℕ} (c : Fin d → F)
    (ab : (Fin (d + 1) → F) × (Fin (d + 1) → F)) :
    (pairTrace c ab).2 ≤ 16 * (d + 1) ^ 2 := by
  have hl := nonconstantTrace_count ab.1
  have hr := nonconstantTrace_count ab.2
  have hp := productTrace_count c ab.1 ab.2
  simp only [pairTrace]
  nlinarith

def evaluateTrace {d : ℕ} (c : Fin d → F) : Bool × ℕ :=
  boolTrace (· && ·) true (pairTrace c) (factorPairs d)

@[simp] theorem evaluateTrace_value {d : ℕ} (c : Fin d → F) :
    (evaluateTrace c).1 = passes c := by
  simp only [evaluateTrace, boolTrace_all_value, pairTrace_value, passes]

theorem evaluateTrace_count {d : ℕ} (c : Fin d → F) :
    (evaluateTrace c).2 ≤ 3 ^ (2 * (d + 1)) * (16 * (d + 1) ^ 2 + 1) := by
  simpa [evaluateTrace] using
    boolTrace_count_le (· && ·) true (pairTrace c) (factorPairs d)
      (16 * (d + 1) ^ 2) (fun ab _ => pairTrace_count c ab)

def searchTrace (d : ℕ) : Option (Fin d → F) × ℕ × ℕ :=
  QuarticSearch.scan evaluateTrace (candidates d)

theorem searchTrace_value (d : ℕ) : (searchTrace d).1 = (search d).1 := by
  simp only [searchTrace, search, QuarticSearch.scan_value, evaluateTrace_value, evaluate_value]

/-- Return the actual coefficients and both counters from one search run. -/
def selectedTrace (d : ℕ) : (Fin d → F) × ℕ × ℕ :=
  let result := searchTrace d
  (result.1.getD (fun _ => 0), result.2)

@[simp] theorem selectedTrace_value (d : ℕ) : (selectedTrace d).1 = coefficients d := by
  simp only [selectedTrace, searchTrace_value, coefficients]

theorem selectedTrace_irreducible {d : ℕ} (hd : 0 < d) :
    Irreducible (QuarticSearch.poly (selectedTrace d).1) := by
  rw [selectedTrace_value]
  exact coefficients_irreducible hd

theorem searchTrace_count (d : ℕ) :
    (searchTrace d).2.2 ≤ 3 ^ (3 * d + 2) * (16 * (d + 1) ^ 2 + 1) := by
  have h := QuarticSearch.scan_tests_le evaluateTrace (candidates d)
    (3 ^ (2 * (d + 1)) * (16 * (d + 1) ^ 2 + 1))
    (fun c _ => evaluateTrace_count c)
  simpa only [searchTrace, length_candidates, ← Nat.mul_assoc, ← pow_add,
    show d + 2 * (d + 1) = 3 * d + 2 by omega] using h

theorem succ_le_three_pow (d : ℕ) : d + 1 ≤ 3 ^ d := by
  induction d with
  | zero => simp
  | succ d ih => rw [pow_succ]; omega

theorem searchTrace_count_exponential (d : ℕ) : (searchTrace d).2.2 ≤ 3 ^ (5 * d + 5) := by
  apply (searchTrace_count d).trans
  have hq : 1 ≤ 3 ^ d := Nat.one_le_pow d 3 (by decide)
  have hp := succ_le_three_pow d
  have hs : (d + 1) ^ 2 ≤ (3 ^ d) ^ 2 := Nat.pow_le_pow_left hp 2
  have hb : 16 * (d + 1) ^ 2 + 1 ≤ 27 * (3 ^ d) ^ 2 := by nlinarith
  calc
    3 ^ (3 * d + 2) * (16 * (d + 1) ^ 2 + 1) ≤
        3 ^ (3 * d + 2) * (27 * (3 ^ d) ^ 2) := Nat.mul_le_mul_left _ hb
    _ = 3 ^ (5 * d + 5) := by
      rw [← pow_mul]
      have h27 : 27 = 3 ^ 3 := by norm_num
      rw [h27, ← pow_add, ← pow_add]
      congr 1
      omega

theorem searchTrace_count_cardinality (d : ℕ) :
    (searchTrace d).2.2 ≤ 243 * (3 ^ d) ^ 5 := by
  apply (searchTrace_count_exponential d).trans_eq
  rw [show 5 * d + 5 = d * 5 + 5 by omega, pow_add, pow_mul]
  norm_num
  ring

/-- When the residue field is the first ternary size above the node count,
the entire counted arithmetic search is polynomial in that count. -/
theorem searchTrace_count_nodeBound (d Q : ℕ) (hd : 3 ^ d ≤ 3 * (Q + 1)) :
    (searchTrace d).2.2 ≤ 59049 * (Q + 1) ^ 5 := by
  calc
    (searchTrace d).2.2 ≤ 243 * (3 ^ d) ^ 5 := searchTrace_count_cardinality d
    _ ≤ 243 * (3 * (Q + 1)) ^ 5 :=
      Nat.mul_le_mul_left 243 (Nat.pow_le_pow_left hd 5)
    _ = 59049 * (Q + 1) ^ 5 := by ring

end SubexponentialSAT.SqrtLog.IrreducibleSearch

end OAI.Algorithms
