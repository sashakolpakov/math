import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.QuarticSearch

namespace OAI.Algorithms

/-!
# Finite coefficient tests for arbitrary-degree irreducible search

Only vectors, finite lists, and scalar arithmetic are executed. `ofFn` and
the polynomial interpretation occur solely in the correctness proofs.
-/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearch

open Polynomial
open scoped BigOperators

abbrev F := ZMod 3

/-- Read a coefficient with zero padding outside the stored vector. -/
def entry {R : Type*} [Zero R] {n : ℕ} (a : Fin n → R) (j : ℕ) : R :=
  if h : j < n then a ⟨j, h⟩ else 0

/-- Ordinary schoolbook convolution, using no polynomial operations. -/
def convolution {R : Type*} [Semiring R] {n : ℕ}
    (a b : Fin n → R) (j : ℕ) : R :=
  ∑ i ∈ Finset.range (j + 1), entry a i * entry b (j - i)

/-- A monic candidate consists of its `d` lower coefficients. -/
def candidateEntry {R : Type*} [Semiring R] {d : ℕ}
    (c : Fin d → R) (j : ℕ) : R :=
  (if j = d then 1 else 0) + entry c j

/-- Test that a stored factor has a nonzero positive-degree coefficient. -/
def nonconstant {n : ℕ} (a : Fin n → F) : Bool :=
  (List.finRange n).any fun i => decide (0 < i.val ∧ a i ≠ 0)

/-- Compare all potentially nonzero product coefficients. -/
def productEq {d : ℕ} (c : Fin d → F) (a b : Fin (d + 1) → F) : Bool :=
  (List.range (2 * d + 1)).all fun j =>
    decide (convolution a b j = candidateEntry c j)

theorem ofFn_coeff_entry {R : Type*} [Semiring R] [DecidableEq R] {n : ℕ}
    (a : Fin n → R) (j : ℕ) : (Polynomial.ofFn n a).coeff j = entry a j := by
  by_cases h : j < n
  · simp [entry, h]
  · simp [entry, h, ofFn_coeff_eq_zero_of_ge a (Nat.le_of_not_gt h)]

theorem convolution_eq_coeff {R : Type*} [CommSemiring R] [DecidableEq R] {n : ℕ}
    (a b : Fin n → R) (j : ℕ) :
    convolution a b j = (Polynomial.ofFn n a * Polynomial.ofFn n b).coeff j := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun x y => (Polynomial.ofFn n a).coeff x * (Polynomial.ofFn n b).coeff y) j]
  simp only [ofFn_coeff_entry, convolution]

theorem poly_eq_X_pow_add_ofFn {R : Type*} [Semiring R] [DecidableEq R] {d : ℕ}
    (c : Fin d → R) :
    QuarticSearch.poly c = X ^ d + Polynomial.ofFn d c := by
  simp only [QuarticSearch.poly, ofFn_eq_sum_monomial, C_mul_X_pow_eq_monomial]

theorem candidateEntry_eq_coeff {R : Type*} [Semiring R] [DecidableEq R] {d : ℕ}
    (c : Fin d → R) (j : ℕ) : candidateEntry c j = (QuarticSearch.poly c).coeff j := by
  rw [poly_eq_X_pow_add_ofFn, coeff_add, coeff_X_pow, ofFn_coeff_entry]
  simp only [candidateEntry, eq_comm]

theorem nonconstant_iff {n : ℕ} (hn : 0 < n) (a : Fin n → F) :
    nonconstant a = true ↔ 0 < (Polynomial.ofFn n a).natDegree := by
  simp only [nonconstant, List.any_eq_true, List.mem_finRange, true_and,
    decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, ha⟩
    have hc : (Polynomial.ofFn n a).coeff i.val ≠ 0 := by simpa using ha
    exact hi.trans_le (le_natDegree_of_ne_zero hc)
  · intro hp
    have hb := Polynomial.ofFn_natDegree_lt hn a
    refine ⟨⟨(Polynomial.ofFn n a).natDegree, hb⟩, hp, ?_⟩
    have hz : Polynomial.ofFn n a ≠ 0 := by
      intro h
      simp [h] at hp
    have hc : (Polynomial.ofFn n a).coeff (Polynomial.ofFn n a).natDegree ≠ 0 :=
      leadingCoeff_ne_zero.mpr hz
    rw [Polynomial.ofFn_coeff_eq_val_of_lt a hb] at hc
    exact hc

theorem productEq_iff {d : ℕ} (c : Fin d → F) (a b : Fin (d + 1) → F) :
    productEq c a b = true ↔
      Polynomial.ofFn (d + 1) a * Polynomial.ofFn (d + 1) b = QuarticSearch.poly c := by
  simp only [productEq, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    convolution_eq_coeff, candidateEntry_eq_coeff]
  constructor
  · intro h
    apply Polynomial.ext
    intro j
    by_cases hj : j < 2 * d + 1
    · exact h j hj
    · have ha : (Polynomial.ofFn (d + 1) a).natDegree ≤ d :=
        Nat.lt_succ_iff.mp (Polynomial.ofFn_natDegree_lt (Nat.succ_pos d) a)
      have hb : (Polynomial.ofFn (d + 1) b).natDegree ≤ d :=
        Nat.lt_succ_iff.mp (Polynomial.ofFn_natDegree_lt (Nat.succ_pos d) b)
      have hm : (Polynomial.ofFn (d + 1) a * Polynomial.ofFn (d + 1) b).natDegree ≤
          (Polynomial.ofFn (d + 1) a).natDegree + (Polynomial.ofFn (d + 1) b).natDegree :=
        Polynomial.natDegree_mul_le
      rw [coeff_eq_zero_of_natDegree_lt (by omega),
        coeff_eq_zero_of_natDegree_lt (by rw [QuarticSearch.poly_natDegree]; omega)]
  · intro h j _
    exact congrArg (fun p : F[X] => p.coeff j) h

end SubexponentialSAT.SqrtLog.IrreducibleSearch

end OAI.Algorithms
