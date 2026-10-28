import OAI.NumberTheory.ArithmeticGroups.Lattices.CommutingNilpotentPolynomials
import Mathlib.Algebra.Algebra.Bilinear

/-! # Exponential Derivative Unipotent -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.ExponentialDerivativeUnipotent.Construction

noncomputable section

/-! At a nilpotent element, the derivative of every sufficiently long
truncated exponential is a unipotent endomorphism of the ambient algebra. -/

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

theorem finiteExponentialDerivative_toLinearMap (m : ℕ) (X : A) :
    (ExponentialDerivative.Construction.finiteExponentialDerivative m X).toLinearMap =
      CommutingNilpotentPolynomials.Construction.exponentialDerivativePolynomial m (LinearMap.mulLeft ℝ X) (LinearMap.mulRight ℝ X) := by
  ext Y
  change ExponentialDerivative.Construction.finiteExponentialDerivative m X Y = _
  rw [ExponentialDerivative.Construction.finiteExponentialDerivative_apply]
  simp only [CommutingNilpotentPolynomials.Construction.exponentialDerivativePolynomial, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.pow_mulLeft, LinearMap.pow_mulRight, Module.End.mul_apply,
    LinearMap.mulLeft_apply, LinearMap.mulRight_apply, mul_assoc]

theorem finiteExponentialDerivative_unipotent (m : ℕ) (X : A) (hX : IsNilpotent X) :
    IsNilpotent ((ExponentialDerivative.Construction.finiteExponentialDerivative (m + 2) X).toLinearMap - 1) := by
  rw [finiteExponentialDerivative_toLinearMap]
  apply CommutingNilpotentPolynomials.Construction.exponentialDerivativePolynomial_unipotent
  · ext Y
    exact (mul_assoc X Y X).symm
  · obtain ⟨k, hk⟩ := hX
    exact ⟨k, by rw [LinearMap.pow_mulLeft, hk, LinearMap.mulLeft_zero_eq_zero]⟩
  · obtain ⟨k, hk⟩ := hX
    exact ⟨k, by rw [LinearMap.pow_mulRight, hk, LinearMap.mulRight_zero_eq_zero]⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.ExponentialDerivativeUnipotent.Construction
