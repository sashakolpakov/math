import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.TotalOrderBasic

namespace OAI.Algorithms

/-! Explicit fixed-length arrays and truncated convolution for the shared marker. -/
namespace SubexponentialSAT.SqrtLog.TotalOrder

open scoped BigOperators
open SubexponentialSAT.Truncation

variable {R : Type*} [CommSemiring R]

/-- Exactly t retained coefficients. This is a finite executable function. -/
abbrev CoeffArray (R : Type*) (t : ℕ) := Fin t → R

/-- Out-of-range reads are zero. -/
def arrayCoeff {t : ℕ} (a : CoeffArray R t) (j : ℕ) : R :=
  if hj : j < t then a ⟨j, hj⟩ else 0

@[simp] theorem arrayCoeff_lt {t j : ℕ} (a : CoeffArray R t) (hj : j < t) :
    arrayCoeff a j = a ⟨j, hj⟩ := by simp [arrayCoeff, hj]

@[simp] theorem arrayCoeff_ge {t j : ℕ} (a : CoeffArray R t) (hj : t ≤ j) :
    arrayCoeff a j = 0 := by simp [arrayCoeff, Nat.not_lt.mpr hj]

/-- Each output coefficient is a finite convolution over i+j=k. -/
def mulArray {t : ℕ} (a b : CoeffArray R t) : CoeffArray R t := fun k =>
  ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k.val,
    arrayCoeff a ij.1 * arrayCoeff b ij.2

def oneArray (t : ℕ) : CoeffArray R t := fun k => if k.val = 0 then 1 else 0

def productArray {t : ℕ} : List (CoeffArray R t) → CoeffArray R t
  | [] => oneArray t
  | a :: as => mulArray a (productArray as)

/-- Summation of the canonical coefficients; not a quotient ring map. -/
def sumArray {t : ℕ} (a : CoeffArray R t) : R := ∑ j : Fin t, a j

/-- Executable row construction, with local coefficients supplied as arrays. -/
def rowArray {t : ℕ} (e : CoeffArray R t) (h : R) : CoeffArray R t :=
  fun j => e j * h ^ j.val

noncomputable section

/-- Polynomial semantics of the finite array. -/
def asPolynomial {t : ℕ} (a : CoeffArray R t) : Polynomial R :=
  ∑ j ∈ Finset.range t, Polynomial.monomial j (arrayCoeff a j)

@[simp] theorem coeff_asPolynomial {t : ℕ} (a : CoeffArray R t) (j : ℕ) :
    (asPolynomial a).coeff j = arrayCoeff a j := by
  classical
  by_cases hj : j < t
  · simp [asPolynomial, Polynomial.coeff_monomial, hj]
  · simp [asPolynomial, Polynomial.coeff_monomial, hj,
      arrayCoeff]

def toArray (t : ℕ) (P : Polynomial R) : CoeffArray R t := fun j => P.coeff j.val

@[simp] theorem toArray_asPolynomial {t : ℕ} (a : CoeffArray R t) :
    toArray t (asPolynomial a) = a := by
  funext j
  simp [toArray, j.isLt]

@[simp] theorem asPolynomial_toArray (t : ℕ) (P : Polynomial R) :
    asPolynomial (toArray t P) = trunc t P := by
  ext j
  by_cases hj : j < t <;> simp [arrayCoeff, toArray, hj]

@[simp] theorem trunc_asPolynomial {t : ℕ} (a : CoeffArray R t) :
    trunc t (asPolynomial a) = asPolynomial a := by
  ext j
  by_cases hj : j < t <;> simp [arrayCoeff, hj]

/-- Explicit convolution is exactly multiplication followed by canonical truncation. -/
theorem asPolynomial_mulArray {t : ℕ} (a b : CoeffArray R t) :
    asPolynomial (mulArray a b) = trunc t (asPolynomial a * asPolynomial b) := by
  ext j
  by_cases hj : j < t
  · simp [ hj, mulArray, Polynomial.coeff_mul]
  · simp [arrayCoeff, hj]

@[simp] theorem asPolynomial_oneArray (t : ℕ) :
    asPolynomial (oneArray t : CoeffArray R t) = trunc t 1 := by
  ext j
  by_cases hj : j < t <;> simp [arrayCoeff, oneArray, hj, Polynomial.coeff_one]

/-- Canonical truncation is stable under a later multiplication and truncation. -/
theorem trunc_mul_trunc (t : ℕ) (P Q : Polynomial R) :
    trunc t (trunc t P * trunc t Q) = trunc t (P * Q) := by
  classical
  ext j
  by_cases hj : j < t
  · simp only [coeff_trunc, ite_eq_left hj, Polynomial.coeff_mul]
    apply Finset.sum_congr rfl
    intro ab hab
    have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    have ha : ab.1 < t := by omega
    have hb : ab.2 < t := by omega
    simp [ha, hb]
  · simp [hj]

theorem trunc_mul_right (t : ℕ) (P Q : Polynomial R) :
    trunc t (P * trunc t Q) = trunc t (P * Q) := by
  classical
  ext j
  by_cases hj : j < t
  · simp only [coeff_trunc, ite_eq_left hj, Polynomial.coeff_mul]
    apply Finset.sum_congr rfl
    intro ab hab
    have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    have hb : ab.2 < t := by omega
    simp [hb]
  · simp [hj]

theorem asPolynomial_productArray {t : ℕ} (as : List (CoeffArray R t)) :
    asPolynomial (productArray as) = trunc t ((as.map asPolynomial).prod) := by
  induction as with
  | nil => simp [productArray]
  | cons a as ih =>
    simp only [productArray, asPolynomial_mulArray, ih, List.map_cons, List.prod_cons]
    exact trunc_mul_right t _ _

theorem sumArray_eq_eval {t : ℕ} (a : CoeffArray R t) :
    sumArray a = (asPolynomial a).eval 1 := by
  classical
  simp only [asPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
    one_pow, mul_one, sumArray]
  simpa only [arrayCoeff_lt _ (Fin.isLt _)] using
    Fin.sum_univ_eq_sum_range (fun j => arrayCoeff a j) t

/-- The executable array loop computes the canonical retained-coefficient sum. -/
theorem sum_productArray_eq {t : ℕ} (as : List (CoeffArray R t)) :
    sumArray (productArray as) =
      (trunc t ((as.map asPolynomial).prod)).eval 1 := by
  rw [sumArray_eq_eval, asPolynomial_productArray]

@[simp] theorem asPolynomial_rowArray {t : ℕ} (e : CoeffArray R t) (h : R) :
    asPolynomial (rowArray e h) = row t (arrayCoeff e) h := by
  ext j
  by_cases hj : j < t <;> simp [arrayCoeff, rowArray, hj]

theorem powerDivisible_rowArray (q : R) {t : ℕ} (e : CoeffArray R t) (h : R)
    (hh : q ∣ h) : SubexponentialSAT.NilpotentDefect.PowerDivisible q (asPolynomial (rowArray e h)) := by
  rw [asPolynomial_rowArray]
  exact powerDivisible_row q t (arrayCoeff e) h hh

/-- General list form of the shared nilpotent total-order identity. -/
theorem sum_productArray_of_powerDivisible (q : R) {t : ℕ}
    (as : List (CoeffArray R t))
    (has : ∀ a ∈ as, SubexponentialSAT.NilpotentDefect.PowerDivisible q (asPolynomial a))
    (hq : q ^ t = 0) :
    sumArray (productArray as) = (as.map sumArray).prod := by
  have hp : SubexponentialSAT.NilpotentDefect.PowerDivisible q ((as.map asPolynomial).prod) := by
    induction as with
    | nil => simpa using SubexponentialSAT.NilpotentDefect.powerDivisible_one q
    | cons a as ih =>
      simp only [List.map_cons, List.prod_cons]
      apply SubexponentialSAT.NilpotentDefect.powerDivisible_mul (has a (List.mem_cons_self))
      exact ih (fun b hb => has b (List.mem_cons_of_mem a hb))
  rw [sum_productArray_eq, trunc_eq_self_of_powerDivisible q t _ hp hq]
  simp only [Polynomial.eval_list_prod, List.map_map, Function.comp_def,
    ← sumArray_eq_eval]

/-- Direct executable form: multiply local rows, keep only total order <t,
and sum; this equals the product of all local exact values. -/
theorem sum_productArray_rows_exact (q : R) {t : ℕ}
    (rs : List (CoeffArray R t × R)) (hh : ∀ a ∈ rs, q ∣ a.2)
    (hq : q ^ t = 0) :
    sumArray (productArray (rs.map (fun a => rowArray a.1 a.2))) =
      (rs.map (fun a => sumArray (rowArray a.1 a.2))).prod := by
  simpa only [List.map_map, Function.comp_def] using
    sum_productArray_of_powerDivisible q (rs.map (fun a => rowArray a.1 a.2)) (by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact powerDivisible_rowArray q b.1 b.2 (hh b hb)) hq

/-- Each coefficient k uses k+1 products; the complete convolution uses at most t². -/
theorem convolution_terms_le_square (t : ℕ) :
    (∑ j ∈ Finset.range t, (Finset.HasAntidiagonal.antidiagonal j).card) ≤ t * t := by
  calc
    _ = ∑ j ∈ Finset.range t, (j + 1) := by simp
    _ ≤ ∑ _j ∈ Finset.range t, t := by
      apply Finset.sum_le_sum
      intro j hj
      exact Nat.succ_le_of_lt (Finset.mem_range.mp hj)
    _ = t * t := by simp

end
end SubexponentialSAT.SqrtLog.TotalOrder

end OAI.Algorithms
