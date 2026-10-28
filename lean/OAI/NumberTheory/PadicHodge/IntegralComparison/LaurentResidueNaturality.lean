import OAI.NumberTheory.PadicHodge.IntegralComparison.LaurentResiduePairing

/-! # Laurent Residue Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.LaurentResidueNaturality

noncomputable section

/-! Multiplication is adjoint for the actual Laurent residue pairing.
The negative-coefficient map is the explicit projection used by the
top cohomology calculation, rather than a duality-chosen operator. -/

open _root_.MvPolynomial

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TwistResidueDuality OAI.NumberTheory.PadicHodge.IntegralComparison.LaurentResiduePairing

universe u

variable (σ : Type) [Fintype σ] (C : Type u) [CommRing C]

def negativeCoefficients (m : ℕ) :
    AddMonoidAlgebra C (σ →₀ ℤ) →ₗ[C] (Projective.TwistResidueDuality.NegativeExponent.{u} σ m → C) where
  toFun f e := f.coeff e.val.val
  map_add' f g := by
    funext e
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, Pi.add_apply]
  map_smul' c f := by
    funext e
    simp only [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, Pi.smul_apply,
      RingHom.id_apply]

theorem residue_polynomial_mul (m : ℕ) (P : homogeneousSubmodule σ C m)
    (f : AddMonoidAlgebra C (σ →₀ ℤ)) :
    LaurentResiduePairing.residue σ C (LaurentResiduePairing.polynomialMap σ C P.val * f) =
      Projective.TwistResidueDuality.polynomialDual σ C m (negativeCoefficients σ C m f) P := by
  classical
  rw [LaurentResiduePairing.polynomialMap_homogeneous, Finset.sum_mul, map_sum, Projective.TwistResidueDuality.polynomialDual_apply]
  apply Finset.sum_congr rfl
  intro e _
  rw [LaurentResiduePairing.residue_apply, AddMonoidAlgebra.coeff_single_mul_apply, LaurentResiduePairing.complementary_exponent]
  rfl

theorem residue_projection (m : ℕ) (P : homogeneousSubmodule σ C m)
    (f : AddMonoidAlgebra C (σ →₀ ℤ)) :
    LaurentResiduePairing.residue σ C (LaurentResiduePairing.polynomialMap σ C P.val *
        LaurentResiduePairing.negativeLaurent σ C m (negativeCoefficients σ C m f)) =
      LaurentResiduePairing.residue σ C (LaurentResiduePairing.polynomialMap σ C P.val * f) := by
  rw [LaurentResiduePairing.residue_product, residue_polynomial_mul]

def homogeneousProduct (a b : ℕ) (P : homogeneousSubmodule σ C a)
    (Q : homogeneousSubmodule σ C b) : homogeneousSubmodule σ C (a + b) :=
  ⟨P.val * Q.val, P.property.mul Q.property⟩

def multiplyNegative (a b : ℕ) (P : homogeneousSubmodule σ C a)
    (v : Projective.TwistResidueDuality.NegativeExponent.{u} σ (a + b) → C) : Projective.TwistResidueDuality.NegativeExponent.{u} σ b → C :=
  negativeCoefficients σ C b (LaurentResiduePairing.polynomialMap σ C P.val * LaurentResiduePairing.negativeLaurent σ C (a + b) v)

theorem multiplication_adjoint (a b : ℕ) (P : homogeneousSubmodule σ C a)
    (Q : homogeneousSubmodule σ C b) (v : Projective.TwistResidueDuality.NegativeExponent.{u} σ (a + b) → C) :
    Projective.TwistResidueDuality.polynomialDual σ C b (multiplyNegative σ C a b P v) Q =
      Projective.TwistResidueDuality.polynomialDual σ C (a + b) v (homogeneousProduct σ C a b P Q) := by
  rw [multiplyNegative, ← residue_polynomial_mul, ← LaurentResiduePairing.residue_product]
  change LaurentResiduePairing.residue σ C (LaurentResiduePairing.polynomialMap σ C Q.val *
      (LaurentResiduePairing.polynomialMap σ C P.val * LaurentResiduePairing.negativeLaurent σ C (a + b) v)) =
    LaurentResiduePairing.residue σ C (LaurentResiduePairing.polynomialMap σ C (P.val * Q.val) * LaurentResiduePairing.negativeLaurent σ C (a + b) v)
  rw [map_mul (LaurentResiduePairing.polynomialMap σ C) P.val Q.val]
  congr 1
  ac_rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.LaurentResidueNaturality
