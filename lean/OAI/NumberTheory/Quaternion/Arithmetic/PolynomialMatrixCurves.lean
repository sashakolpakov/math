import OAI.NumberTheory.Quaternion.Arithmetic.BinomialPolynomials
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Polynomial Matrix Curves -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.PolynomialMatrixCurves

noncomputable section

section

/-! Polynomial matrix curves are determined by their natural-number
values. A curve interpolating powers therefore satisfies the additive
one-parameter group law over the entire field. -/

open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

def evalPolynomialMatrix (P : Matrix (Fin n) (Fin n) (Polynomial K)) (t : K) :
    Matrix (Fin n) (Fin n) K := P.map (Polynomial.evalRingHom t)

def translatePolynomialMatrix (P : Matrix (Fin n) (Fin n) (Polynomial K)) (t : K) :
    Matrix (Fin n) (Fin n) (Polynomial K) :=
  P.map (fun p => p.comp (Polynomial.X + Polynomial.C t))

omit [CharZero K] in
theorem evalPolynomialMatrix_translate (P : Matrix (Fin n) (Fin n) (Polynomial K)) (t x : K) :
    evalPolynomialMatrix (translatePolynomialMatrix P t) x = evalPolynomialMatrix P (x + t) := by
  ext i j
  simp [evalPolynomialMatrix, translatePolynomialMatrix, Polynomial.eval_comp]

omit [CharZero K] in
theorem evalPolynomialMatrix_constant (M : Matrix (Fin n) (Fin n) K) (t : K) :
    evalPolynomialMatrix (M.map Polynomial.C) t = M := by
  ext i j
  exact Polynomial.eval_C

omit [CharZero K] in
theorem evalPolynomialMatrix_mul (P Q : Matrix (Fin n) (Fin n) (Polynomial K)) (t : K) :
    evalPolynomialMatrix (P * Q) t = evalPolynomialMatrix P t * evalPolynomialMatrix Q t :=
  Matrix.map_mul

theorem polynomialMatrix_eq_of_nat_evaluations (P Q : Matrix (Fin n) (Fin n) (Polynomial K))
    (h : ∀ m : ℕ, evalPolynomialMatrix P (m : K) = evalPolynomialMatrix Q (m : K)) : P = Q := by
  apply Matrix.ext
  intro i j
  apply BinomialPolynomials.polynomial_eq_of_nat_evaluations
  intro m
  exact congrFun (congrFun (h m) i) j

theorem polynomialMatrix_add_law_of_nat_powers
    (P : Matrix (Fin n) (Fin n) (Polynomial K)) (g : Matrix (Fin n) (Fin n) K)
    (hP : ∀ m : ℕ, evalPolynomialMatrix P (m : K) = g ^ m) (s t : K) :
    evalPolynomialMatrix P (s + t) = evalPolynomialMatrix P s * evalPolynomialMatrix P t := by
  have hn (m : ℕ) : translatePolynomialMatrix P (m : K) = P * ((g ^ m).map Polynomial.C) := by
    apply polynomialMatrix_eq_of_nat_evaluations
    intro k
    rw [evalPolynomialMatrix_translate, ← Nat.cast_add, hP, pow_add,
      evalPolynomialMatrix_mul, evalPolynomialMatrix_constant, hP]
  have hshift (x : K) (m : ℕ) : evalPolynomialMatrix P (x + (m : K)) =
      evalPolynomialMatrix P x * g ^ m := by
    rw [← evalPolynomialMatrix_translate, hn, evalPolynomialMatrix_mul, evalPolynomialMatrix_constant]
  have hs : translatePolynomialMatrix P s = (evalPolynomialMatrix P s).map Polynomial.C * P := by
    apply polynomialMatrix_eq_of_nat_evaluations
    intro m
    rw [evalPolynomialMatrix_translate, add_comm, hshift, evalPolynomialMatrix_mul,
      evalPolynomialMatrix_constant, hP]
  rw [add_comm s t, ← evalPolynomialMatrix_translate, hs, evalPolynomialMatrix_mul,
    evalPolynomialMatrix_constant]

end

/-! A unipotent matrix's natural powers are the values of one
polynomial matrix curve, using the finite binomial expansion. -/

open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

def nilpotentPowerPolynomial (N : Matrix (Fin n) (Fin n) K) (d : ℕ) :
    Matrix (Fin n) (Fin n) (Polynomial K) :=
  fun i j => ∑ k ∈ Finset.range d,
    BinomialPolynomials.binomialCoefficientPolynomial (K := K) k * Polynomial.C ((N ^ k) i j)

theorem nilpotentPowerPolynomial_eval_nat (N : Matrix (Fin n) (Fin n) K) (d : ℕ)
    (hd : N ^ d = 0) (m : ℕ) :
    evalPolynomialMatrix (nilpotentPowerPolynomial N d) (m : K) = (1 + N) ^ m := by
  apply Eq.trans ?_ (BinomialPolynomials.nilpotent_binomial_sum_nat (K := K) N d hd m)
  ext i j
  simp [evalPolynomialMatrix, nilpotentPowerPolynomial, BinomialPolynomials.binomialCoefficientPolynomial_eval_nat,
    Matrix.sum_apply, Polynomial.eval_finsetSum]

theorem unipotent_has_polynomial_powers (g : Matrix (Fin n) (Fin n) K) (hg : IsNilpotent (g - 1)) :
    ∃ P : Matrix (Fin n) (Fin n) (Polynomial K), ∀ m : ℕ, evalPolynomialMatrix P (m : K) = g ^ m := by
  obtain ⟨d, hd⟩ := hg
  refine ⟨nilpotentPowerPolynomial (g - 1) d, fun m => ?_⟩
  have he : 1 + (g - 1) = g := by abel
  simpa only [he] using nilpotentPowerPolynomial_eval_nat (g - 1) d hd m

end

end OAI.NumberTheory.Quaternion.Arithmetic.PolynomialMatrixCurves
