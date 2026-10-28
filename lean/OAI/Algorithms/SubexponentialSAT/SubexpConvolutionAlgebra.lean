import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.TruncatedConvolution
import OAI.Algorithms.SubexponentialSAT.PolynomialAlgorithm
import OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic

namespace OAI.Algorithms

/-! Polynomial semantics of the triangular update schedule used by the
actual convolution controller. This file assigns no execution costs. -/

namespace SubexponentialSAT.SubexpConvolutionAlgebra

open Polynomial
open TruncatedConvolution

namespace PA
export PolynomialAlgorithm (denote)
end PA

section Algebra

variable {R : Type*} [CommSemiring R]

theorem denote_modify_add (acc : List R) (i : ℕ) (a : R) (hi : i < acc.length) :
    PA.denote (acc.modify i (fun c => a + c)) = PA.denote acc + monomial i a := by
  induction acc generalizing i with
  | nil => simp at hi
  | cons c cs ih =>
      cases i with
      | zero =>
          simp only [List.modify_zero_cons, PolynomialAlgorithm.denote_cons,
            monomial_zero_left, map_add]
          ring
      | succ i =>
          simp only [List.modify_succ_cons, PolynomialAlgorithm.denote_cons]
          rw [ih i (by simpa using hi), mul_add, X_mul_monomial]
          ring

theorem denote_addProduct (i : ℕ) (a b : R) (acc : List R) (hi : i < acc.length) :
    PA.denote (addProduct (· + ·) (· * ·) i a b acc) =
      PA.denote acc + monomial i (a * b) :=
  denote_modify_add acc i (a * b) hi

theorem denote_row (a : R) (i : ℕ) (Q acc : List R)
    (hfit : i + Q.length ≤ acc.length) :
    PA.denote (row (· + ·) (· * ·) a i Q acc) =
      PA.denote acc + X ^ i * C a * PA.denote Q := by
  induction Q generalizing i acc with
  | nil => simp [row]
  | cons b bs ih =>
      rw [row, ih]
      · rw [denote_addProduct i a b acc (by simp only [List.length_cons] at hfit; omega),
          PolynomialAlgorithm.denote_cons, ← C_mul_X_pow_eq_monomial, map_mul, pow_succ]
        ring
      · simp only [addProduct_length]
        simp only [List.length_cons] at hfit
        omega

theorem trunc_C_mul (D : ℕ) (a : R) (P : Polynomial R) :
    Truncation.trunc D (C a * P) = C a * Truncation.trunc D P := by
  ext n
  by_cases hn : n < D <;> simp [Truncation.coeff_trunc, coeff_C_mul, hn]

theorem trunc_X_mul (D : ℕ) (P : Polynomial R) :
    Truncation.trunc (D + 1) (X * P) = X * Truncation.trunc D P := by
  ext n
  cases n <;> simp [Truncation.coeff_trunc, coeff_X_mul]

theorem trunc_zero_order (P : Polynomial R) : Truncation.trunc 0 P = 0 := by
  ext n
  simp

theorem denote_rows (Q : List R) (i fuel : ℕ) (P acc : List R)
    (hfit : i + fuel ≤ acc.length) :
    PA.denote (rows (· + ·) (· * ·) Q i fuel P acc) =
      PA.denote acc + X ^ i * Truncation.trunc fuel (PA.denote P * PA.denote Q) := by
  induction fuel generalizing i P acc with
  | zero => simp [rows, trunc_zero_order]
  | succ fuel ih =>
      cases P with
      | nil => simp [rows]
      | cons a rest =>
          rw [rows, ih]
          · rw [denote_row]
            · rw [show PA.denote (Q.take (fuel + 1)) =
                  Truncation.trunc (fuel + 1) (PA.denote Q) from
                    PolynomialAlgorithm.denote_truncate (fuel + 1) Q]
              simp only [PolynomialAlgorithm.denote_cons, add_mul, mul_assoc,
                Truncation.trunc_add, trunc_C_mul, trunc_X_mul, pow_succ]
              ring
            · simp only [List.length_take]
              omega
          · simp only [row_length]
            omega

@[simp] theorem denote_replicate_zero (D : ℕ) :
    PA.denote (List.replicate D (0 : R)) = 0 := by
  induction D with
  | zero => rfl
  | succ D ih => simp [List.replicate_succ, ih]

/-- The actual schedule computes the degree-below-D part of the product,
with exactly D stored coefficients, including trailing zeros. -/
theorem run_denote (D : ℕ) (P Q : List R) :
    PA.denote (run 0 (· + ·) (· * ·) D P Q) =
      Truncation.trunc D (PA.denote P * PA.denote Q) := by
  rw [run, denote_rows Q 0 D P _ (by simp)]
  simp

end Algebra

section Decode

variable {C R : Type*} [CommSemiring R]
    (decode : C → R) (add mul : C → C → C)
    (hadd : ∀ a b, decode (add a b) = decode a + decode b)
    (hmul : ∀ a b, decode (mul a b) = decode a * decode b)

include hadd hmul

theorem map_addProduct (i : ℕ) (a b : C) (acc : List C) :
    (addProduct add mul i a b acc).map decode =
      addProduct (· + ·) (· * ·) i (decode a) (decode b) (acc.map decode) := by
  induction acc generalizing i with
  | nil => simp [addProduct]
  | cons c cs ih =>
      cases i with
      | zero => simp [addProduct, hadd, hmul]
      | succ i => simpa [addProduct] using congrArg (decode c :: ·) (ih i)

theorem map_row (a : C) (i : ℕ) (Q acc : List C) :
    (row add mul a i Q acc).map decode =
      row (· + ·) (· * ·) (decode a) i (Q.map decode) (acc.map decode) := by
  induction Q generalizing i acc with
  | nil => rfl
  | cons b bs ih =>
      simp only [row, List.map_cons, ih, map_addProduct decode add mul hadd hmul]

theorem map_rows (Q : List C) (i fuel : ℕ) (P acc : List C) :
    (rows add mul Q i fuel P acc).map decode =
      rows (· + ·) (· * ·) (Q.map decode) i fuel (P.map decode) (acc.map decode) := by
  induction fuel generalizing i P acc with
  | zero => rfl
  | succ fuel ih =>
      cases P with
      | nil => rfl
      | cons a rest =>
          simp only [rows, List.map_cons, ih, map_row decode add mul hadd hmul, List.map_take]

theorem run_correct (zero : C) (hzero : decode zero = 0) (D : ℕ) (P Q : List C) :
    PA.denote ((run zero add mul D P Q).map decode) =
      Truncation.trunc D (PA.denote (P.map decode) * PA.denote (Q.map decode)) := by
  simp only [run, map_rows decode add mul hadd hmul, List.map_replicate, hzero]
  exact run_denote D (P.map decode) (Q.map decode)

end Decode

/-- The generic refinement specializes to the concrete prepared binary
quartic operations used by the machine controller. -/
theorem prepared_run_correct (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ)
    (c : Fin 4 → ZMod (p ^ μ))
    (t z : SubexpQuarticRing.Quad (SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p μ)))
    (ht : t.map (SubexpQuarticRing.wordValue p μ) = SubexpQuarticRing.reductionData c)
    (hz : SubexpQuarticRing.quotientDenote c (z.map (SubexpQuarticRing.wordValue p μ)) = 0)
    (D : ℕ)
    (P Q : List (SubexpQuarticRing.Quad
      (SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p μ)))) :
    let decode := fun a : SubexpQuarticRing.Quad
      (SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p μ)) => SubexpQuarticRing.quotientDenote c
      (a.map (SubexpQuarticRing.wordValue p μ))
    PA.denote ((run z
      (fun a b => (SubexpPreparedQuartic.binaryAdd p μ M a b).1)
      (fun a b => (SubexpPreparedQuartic.binaryMul p μ M t a b).1) D P Q).map decode) =
        Truncation.trunc D (PA.denote (P.map decode) * PA.denote (Q.map decode)) := by
  apply run_correct
  · exact SubexpPreparedQuartic.binaryAdd_quotient p μ M c
  · intro a b
    exact SubexpPreparedQuartic.binaryMul_quotient p μ M c t a b ht
  · exact hz

end SubexponentialSAT.SubexpConvolutionAlgebra

end OAI.Algorithms
