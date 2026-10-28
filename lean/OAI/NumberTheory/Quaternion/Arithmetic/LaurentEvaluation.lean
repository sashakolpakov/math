import OAI.NumberTheory.ArithmeticGroups.Lattices.Laurent
import OAI.NumberTheory.Quaternion.Arithmetic.BinomialPolynomials

/-! # Laurent Evaluation -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.LaurentEvaluation

noncomputable section

section

/-! Laurent polynomials over characteristic-zero fields are determined
by evaluation at nonzero field elements. -/

open scoped Classical LaurentPolynomial
open LaurentPolynomial

theorem laurent_eq_zero_of_unit_evaluations
    {K : Type*} [Field K] [CharZero K] (p : LaurentPolynomial K)
    (hp : ∀ t : Kˣ, LaurentPolynomial.eval₂ (RingHom.id K) t p = 0) : p = 0 := by
  obtain ⟨d, P, hP⟩ := p.exists_T_pow
  have hPX : P * Polynomial.X = 0 := by
    apply BinomialPolynomials.polynomial_eq_of_nat_evaluations
    intro m
    by_cases hm : m = 0
    · subst m
      simp
    · let t : Kˣ := Units.mk0 (m : K) (Nat.cast_ne_zero.mpr hm)
      have he := congrArg (LaurentPolynomial.eval₂ (RingHom.id K) t) hP
      rw [LaurentPolynomial.eval₂_toLaurent, Polynomial.eval₂_id, map_mul, hp, zero_mul] at he
      change P.eval (m : K) = 0 at he
      rw [Polynomial.eval_mul, he, zero_mul, Polynomial.eval_zero]
  have hP0 : P = 0 := (mul_eq_zero.mp hPX).resolve_right Polynomial.X_ne_zero
  have he : p * LaurentPolynomial.T d = 0 := by rw [← hP, hP0, map_zero]
  exact (LaurentPolynomial.isUnit_T (R := K) d).mul_left_eq_zero.mp he

theorem laurent_eq_of_unit_evaluations
    {K : Type*} [Field K] [CharZero K] (p q : LaurentPolynomial K)
    (hpq : ∀ t : Kˣ, LaurentPolynomial.eval₂ (RingHom.id K) t p =
      LaurentPolynomial.eval₂ (RingHom.id K) t q) : p = q := by
  apply sub_eq_zero.mp
  apply laurent_eq_zero_of_unit_evaluations
  intro t
  rw [map_sub, hpq, sub_self]

theorem laurent_eq_sum_coefficients
    {K : Type*} [Field K] (p : LaurentPolynomial K) :
    p = ∑ z ∈ p.coeff.support, LaurentPolynomial.C (p.coeff z) * LaurentPolynomial.T z := by
  apply LaurentPolynomial.ext
  intro z
  simp only [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_sum,
    AddMonoidAlgebra.coeff_single, Finset.sum_apply']
  rw [Finset.sum_eq_single z]
  · simp
  · intro w _ hw
    simp [hw]
  · intro hz
    simp [Finsupp.notMem_support_iff.mp hz]

end

/-! Rescaling a Laurent-polynomial parameter multiplies its weight-z
coefficient by the z-th power of the scaling unit. -/

open scoped Classical LaurentPolynomial

def laurentWeightScale {K : Type*} [Field K] (s : Kˣ) (p : LaurentPolynomial K) :
    LaurentPolynomial K :=
  ∑ z ∈ p.coeff.support,
    LaurentPolynomial.C (p.coeff z * (s ^ z).val) * LaurentPolynomial.T z

theorem laurentWeightScale_coeff {K : Type*} [Field K]
    (s : Kˣ) (p : LaurentPolynomial K) (z : ℤ) :
    (laurentWeightScale s p).coeff z = p.coeff z * (s ^ z).val := by
  simp only [laurentWeightScale, ← LaurentPolynomial.single_eq_C_mul_T,
    AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single, Finset.sum_apply']
  rw [Finset.sum_eq_single z]
  · simp
  · intro w _ hw
    simp [hw]
  · intro hz
    simp [Finsupp.notMem_support_iff.mp hz]

theorem laurentWeightScale_eval {K : Type*} [Field K]
    (s t : Kˣ) (p : LaurentPolynomial K) :
    LaurentPolynomial.eval₂ (RingHom.id K) t (laurentWeightScale s p) =
      LaurentPolynomial.eval₂ (RingHom.id K) (s * t) p := by
  conv_rhs => rw [laurent_eq_sum_coefficients p]
  simp only [laurentWeightScale, map_sum, LaurentPolynomial.eval₂_C_mul_T,
    RingHom.id_apply, mul_zpow, Units.val_mul]
  apply Finset.sum_congr rfl
  intro z _
  exact mul_assoc _ _ _

theorem laurent_constant_mul_coeff {K : Type*} [Field K]
    (a : K) (p : LaurentPolynomial K) (z : ℤ) :
    (LaurentPolynomial.C a * p).coeff z = a * p.coeff z :=
  AddMonoidAlgebra.coeff_single_zero_mul p a z

end

end OAI.NumberTheory.Quaternion.Arithmetic.LaurentEvaluation
