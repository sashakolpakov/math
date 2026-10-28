import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.Algebra.Algebra.Hom

/-! # Nilpotent Derivation Exp -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.NilpotentDerivationExp

noncomputable section

/-! The finite exponential of a nilpotent derivation is an algebra
homomorphism; on vectors killed by its square it is the linear truncation. -/

open scoped Classical

variable {F A : Type*} [Field F] [CharZero F] [Ring A] [Algebra F A]
  [Algebra ℚ A] [IsScalarTower ℚ F A]

omit [CharZero F] [IsScalarTower ℚ F A] in
theorem nilpotent_exp_apply_of_square_zero (D : Module.End F A) (hD : IsNilpotent D)
    (x : A) (hx : D (D x) = 0) : IsNilpotent.exp D x = x + D x := by
  have h : (D ^ 2) • x = 0 := by
    change (D * D) x = 0
    exact hx
  have he := IsNilpotent.exp_smul_eq_sum h hD
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, one_smul] using! he

omit [CharZero F] [IsScalarTower ℚ F A] in
theorem nilpotent_exp_apply_of_zero (D : Module.End F A) (hD : IsNilpotent D)
    (x : A) (hx : D x = 0) : IsNilpotent.exp D x = x := by
  have he := nilpotent_exp_apply_of_square_zero D hD x (by rw [hx, map_zero])
  simpa only [hx, add_zero] using he

def nilpotentDerivationExp (D : Module.End F A) (hD : IsNilpotent D)
    (h₁ : D 1 = 0) (hder : ∀ x y, D (x * y) = x * D y + D x * y) : A →ₐ[F] A :=
  AlgHom.ofLinearMap (IsNilpotent.exp D) (nilpotent_exp_apply_of_zero D hD 1 h₁)
    (Module.End.exp_mul_of_derivation F A D hder hD)

end

end OAI.NumberTheory.Quaternion.Arithmetic.NilpotentDerivationExp
