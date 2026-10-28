import OAI.NumberTheory.ArithmeticGroups.Lattices.NilpotentExponentialPolynomial
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-! # Exponential Derivative -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.ExponentialDerivative.Construction

noncomputable section

/-! The strict derivative of the finite exponential polynomial,
valid in a noncommutative real normed algebra. -/

open scoped RightActions

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def finiteExponentialPolynomial (m : ℕ) (X : A) : A :=
  ∑ n ∈ Finset.range m, (n.factorial⁻¹ : ℝ) • X ^ n

def finiteExponentialDerivative (m : ℕ) (X : A) : A →L[ℝ] A :=
  ∑ n ∈ Finset.range m, (n.factorial⁻¹ : ℝ) •
    ∑ i ∈ Finset.range n, X ^ (n.pred - i) •> ContinuousLinearMap.id ℝ A <• X ^ i

theorem hasStrictFDerivAt_finiteExponentialPolynomial (m : ℕ) (X : A) :
    HasStrictFDerivAt (finiteExponentialPolynomial m) (finiteExponentialDerivative m X) X := by
  apply HasStrictFDerivAt.fun_sum
  intro n _
  exact (hasStrictFDerivAt_pow' (𝕜 := ℝ) n).const_smul (n.factorial⁻¹ : ℝ)

theorem finiteExponentialDerivative_apply (m : ℕ) (X Y : A) :
    finiteExponentialDerivative m X Y =
      ∑ n ∈ Finset.range m, (n.factorial⁻¹ : ℝ) •
        ∑ i ∈ Finset.range n, X ^ (n.pred - i) * Y * X ^ i := by
  simp only [finiteExponentialDerivative, sum_apply, smul_apply]
  rfl

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.ExponentialDerivative.Construction
