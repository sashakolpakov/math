import OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.ExponentialDerivativeUnipotent
import OAI.NumberTheory.ArithmeticGroups.Lattices.NilpotentExponentialUnipotent

/-! # Left Exponential Derivative -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.LeftExponentialDerivative.Construction

noncomputable section

/-! Multiplying the exponential derivative by the inverse exponential
gives another unipotent endomorphism at every nilpotent element. -/

open NormedSpace

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def leftExponentialDerivative (m : ℕ) (X : A) : A →L[ℝ] A :=
  (ContinuousLinearMap.mul ℝ A (exp (-X))).comp (Finite.ExponentialDerivative.Construction.finiteExponentialDerivative m X)

theorem leftExponentialDerivative_apply (m : ℕ) (X Y : A) :
    leftExponentialDerivative m X Y = exp (-X) * Finite.ExponentialDerivative.Construction.finiteExponentialDerivative m X Y := rfl

theorem leftExponentialDerivative_unipotent (m : ℕ) (X : A) (hX : IsNilpotent X) :
    IsNilpotent ((leftExponentialDerivative (m + 2) X).toLinearMap - 1) := by
  change IsNilpotent (LinearMap.mulLeft ℝ (exp (-X)) *
    (Finite.ExponentialDerivative.Construction.finiteExponentialDerivative (m + 2) X).toLinearMap - 1)
  apply CommutingNilpotentPolynomials.Construction.commuting_unipotent_product
  · have hL : Commute (LinearMap.mulLeft ℝ (exp (-X))) (LinearMap.mulLeft ℝ X) := by
      ext Y
      change exp (-X) * (X * Y) = X * (exp (-X) * Y)
      rw [← mul_assoc, ((Commute.refl X).neg_left.exp_left).eq, mul_assoc]
    have hR : Commute (LinearMap.mulLeft ℝ (exp (-X))) (LinearMap.mulRight ℝ X) := by
      ext Y
      exact (mul_assoc (exp (-X)) Y X).symm
    rw [Finite.ExponentialDerivativeUnipotent.Construction.finiteExponentialDerivative_toLinearMap, CommutingNilpotentPolynomials.Construction.exponentialDerivativePolynomial]
    apply Commute.sum_right
    intro n _
    apply Commute.smul_right
    apply Commute.sum_right
    intro i _
    exact (hL.pow_right _).mul_right (hR.pow_right _)
  · have h := (NilpotentExponentialUnipotent.Construction.nilpotent_exponential_sub_one (-X) hX.neg).map (Algebra.lmul ℝ A)
    simpa only [map_sub, map_one] using! h
  · exact Finite.ExponentialDerivativeUnipotent.Construction.finiteExponentialDerivative_unipotent m X hX

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.LeftExponentialDerivative.Construction
