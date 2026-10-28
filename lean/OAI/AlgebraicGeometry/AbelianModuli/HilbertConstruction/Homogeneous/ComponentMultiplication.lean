import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.MultiplicationMatrices

/-! # Component Multiplication -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ComponentMultiplication

noncomputable section

/-! Multiplication by a variable shifts homogeneous components by one degree. -/

universe u v

variable {R : Type u} [CommRing R] {σ : Type v}
attribute [local instance] MvPolynomial.gradedAlgebra

def homogeneousComponentSection (d : ℕ) : MvPolynomial σ R →ₗ[R]
    MvPolynomial.homogeneousSubmodule σ R d :=
  (MvPolynomial.homogeneousComponent d).codRestrict _ (MvPolynomial.homogeneousComponent_mem d)

theorem homogeneous_decompose_eq_component (p : MvPolynomial σ R) (d : ℕ) :
    (DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ R) p d : MvPolynomial σ R) =
      MvPolynomial.homogeneousComponent d p :=
  MvPolynomial.decomposition.decompose'_apply p d

theorem homogeneousComponent_variable_mul_succ (i : σ) (p : MvPolynomial σ R) (d : ℕ) :
    MvPolynomial.homogeneousComponent (d + 1) (MvPolynomial.X i * p) =
      MvPolynomial.X i * MvPolynomial.homogeneousComponent d p := by
  have h := DirectSum.coe_decompose_mul_add_of_left_mem
    (MvPolynomial.homogeneousSubmodule σ R) (i := 1) (j := d) (b := p)
    (MvPolynomial.isHomogeneous_X R i)
  rw [homogeneous_decompose_eq_component, homogeneous_decompose_eq_component] at h
  simpa only [Nat.add_comm] using h

theorem homogeneousComponent_variable_mul_zero (i : σ) (p : MvPolynomial σ R) :
    MvPolynomial.homogeneousComponent 0 (MvPolynomial.X i * p) = 0 := by
  have h := DirectSum.coe_decompose_mul_of_left_mem_of_not_le
    (MvPolynomial.homogeneousSubmodule σ R) (b := p)
    (MvPolynomial.isHomogeneous_X R i) (show ¬1 ≤ (0 : ℕ) by omega)
  rw [homogeneous_decompose_eq_component] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ComponentMultiplication
