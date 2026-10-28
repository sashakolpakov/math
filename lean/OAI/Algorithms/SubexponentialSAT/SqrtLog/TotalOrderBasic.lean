import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Truncation

namespace OAI.Algorithms

/-!
# Shared total-order truncation of nilpotent expansions

The outer variable is a formal marker U. `output` evaluates the canonical
representative after truncation at U = 1. This is an additive operation on
polynomials, not a homomorphism out of the quotient by U^t.
-/
namespace SubexponentialSAT.SqrtLog.TotalOrder

noncomputable section

open scoped BigOperators
open SubexponentialSAT.Truncation SubexponentialSAT.NilpotentDefect

variable {R S α : Type*} [CommSemiring R] [CommSemiring S]

/-- A finite expansion whose s-th coefficient carries s powers of h. -/
def row (t : ℕ) (e : ℕ → R) (h : R) : Polynomial R :=
  ∑ j ∈ Finset.range t, Polynomial.monomial j (e j * h ^ j)

@[simp] theorem coeff_row (t j : ℕ) (e : ℕ → R) (h : R) :
    (row t e h).coeff j = if j < t then e j * h ^ j else 0 := by
  classical
  simp [row, Polynomial.coeff_monomial]

/-- The full product is a semantic object; the executable version uses arrays. -/
def fullProduct (s : Finset α) (t : ℕ) (e : α → ℕ → R) (h : α → R) :
    Polynomial R := ∏ i ∈ s, row t (e i) (h i)

/-- The unique chosen representative has U-degree strictly below t. -/
def retainedProduct (s : Finset α) (t : ℕ) (e : α → ℕ → R) (h : α → R) :
    Polynomial R := trunc t (fullProduct s t e h)

/-- Evaluation applies to the chosen polynomial representative only. -/
def output (s : Finset α) (t : ℕ) (e : α → ℕ → R) (h : α → R) : R :=
  (retainedProduct s t e h).eval 1

theorem trunc_eq_sum (t : ℕ) (P : Polynomial R) :
    trunc t P = ∑ j ∈ Finset.range t, Polynomial.monomial j (P.coeff j) := by
  classical
  ext j
  simp [ Polynomial.coeff_monomial]

theorem eval_one_trunc (t : ℕ) (P : Polynomial R) :
    (trunc t P).eval 1 = ∑ j ∈ Finset.range t, P.coeff j := by
  rw [trunc_eq_sum]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial, one_pow, mul_one]

/-- A linear coefficient sum; no multiplicativity is asserted. -/
def sumRetainedAddHom (t : ℕ) : Polynomial R →+ R :=
  (Polynomial.evalRingHom (1 : R)).toAddMonoidHom.comp (truncAddHom t)

@[simp] theorem sumRetainedAddHom_apply (t : ℕ) (P : Polynomial R) :
    sumRetainedAddHom t P = ∑ j ∈ Finset.range t, P.coeff j :=
  eval_one_trunc t P

theorem output_eq_sum_coeff (s : Finset α) (t : ℕ)
    (e : α → ℕ → R) (h : α → R) :
    output s t e h = ∑ j ∈ Finset.range t, (fullProduct s t e h).coeff j :=
  eval_one_trunc t _

@[simp] theorem map_row (f : R →+* S) (t : ℕ) (e : ℕ → R) (h : R) :
    (row t e h).map f = row t (fun j => f (e j)) (f h) := by
  classical
  simp [row, Polynomial.map_sum]

@[simp] theorem map_trunc (f : R →+* S) (t : ℕ) (P : Polynomial R) :
    (trunc t P).map f = trunc t (P.map f) := by
  ext j
  by_cases hj : j < t <;> simp [hj]

@[simp] theorem map_fullProduct (f : R →+* S) (s : Finset α) (t : ℕ)
    (e : α → ℕ → R) (h : α → R) :
    (fullProduct s t e h).map f =
      fullProduct s t (fun i j => f (e i j)) (fun i => f (h i)) := by
  classical
  simp [fullProduct, Polynomial.map_prod]

theorem map_output (f : R →+* S) (s : Finset α) (t : ℕ)
    (e : α → ℕ → R) (h : α → R) :
    f (output s t e h) =
      output s t (fun i j => f (e i j)) (fun i => f (h i)) := by
  simp only [output_eq_sum_coeff, map_sum]
  congr 1
  funext j
  simpa only [Polynomial.coeff_map] using
    congrArg (fun P : Polynomial S => P.coeff j) (map_fullProduct f s t e h)

/-- Each row has the divisibility invariant needed to kill discarded terms. -/
theorem powerDivisible_row (q : R) (t : ℕ) (e : ℕ → R) (h : R)
    (hh : q ∣ h) : PowerDivisible q (row t e h) := by
  intro j
  rw [coeff_row]
  split_ifs
  · exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hh j) _
  · exact dvd_zero _

theorem powerDivisible_fullProduct (q : R) (s : Finset α) (t : ℕ)
    (e : α → ℕ → R) (h : α → R) (hh : ∀ i ∈ s, q ∣ h i) :
    PowerDivisible q (fullProduct s t e h) := by
  apply powerDivisible_prod
  intro i hi
  exact powerDivisible_row q t (e i) (h i) (hh i hi)

/-- An arbitrary power-divisible polynomial loses no terms after the generator
becomes nilpotent. This is an equality of canonical representatives. -/
theorem trunc_eq_self_of_powerDivisible (q : R) (t : ℕ) (P : Polynomial R)
    (hP : PowerDivisible q P) (hq : q ^ t = 0) : trunc t P = P := by
  ext j
  rw [coeff_trunc]
  split_ifs with hj
  · rfl
  · symm
    exact high_coeff_eq_zero hP hq j (Nat.le_of_not_gt hj)

/-- After substitution into a nilpotent setting, EVERY discarded coefficient
vanishes; therefore truncating the shared total order is exact. -/
theorem retainedProduct_eq_fullProduct (q : R) (s : Finset α) (t : ℕ)
    (e : α → ℕ → R) (h : α → R) (hh : ∀ i ∈ s, q ∣ h i)
    (hq : q ^ t = 0) :
    retainedProduct s t e h = fullProduct s t e h := by
  ext j
  change (trunc t (fullProduct s t e h)).coeff j = _
  rw [coeff_trunc]
  split_ifs with hj
  · rfl
  · symm
    exact high_coeff_eq_zero (powerDivisible_fullProduct q s t e h hh) hq j
      (Nat.le_of_not_gt hj)

/-- The exact shared truncation equals the product of local exact values. -/
theorem output_eq_prod (q : R) (s : Finset α) (t : ℕ)
    (e : α → ℕ → R) (h : α → R) (hh : ∀ i ∈ s, q ∣ h i)
    (hq : q ^ t = 0) :
    output s t e h = ∏ i ∈ s, (∑ j ∈ Finset.range t, e i j * h i ^ j) := by
  unfold output
  rw [retainedProduct_eq_fullProduct q s t e h hh hq]
  simp only [fullProduct, row, Polynomial.eval_prod, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, one_pow, mul_one]

/-- Apply after evaluating symbolic coefficients at an actual input. -/
theorem map_output_eq_prod (f : R →+* S) (q : S) (s : Finset α) (t : ℕ)
    (e : α → ℕ → R) (h : α → R) (hh : ∀ i ∈ s, q ∣ f (h i))
    (hq : q ^ t = 0) :
    f (output s t e h) =
      ∏ i ∈ s, (∑ j ∈ Finset.range t, f (e i j) * f (h i) ^ j) := by
  rw [map_output]
  exact output_eq_prod q s t _ _ hh hq

end

end SubexponentialSAT.SqrtLog.TotalOrder

end OAI.Algorithms
