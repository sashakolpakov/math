import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Form Monomial Basis -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.FormMonomialBasis.PolynomialFormMonomialBasis

noncomputable section

/-! # Monomial and ordered exterior bases of polynomial forms -/

open scoped TensorProduct

universe u

variable (R σ : Type u) [CommRing R] [LinearOrder σ]

abbrev Index (n : ℕ) := (σ →₀ ℕ) × Set.powersetCard σ n

def basis (n : ℕ) : Module.Basis (Index σ n) R
    (Koszul.Tensor.KoszulTensor.Term R σ (MvPolynomial σ R) n) :=
  (MvPolynomial.basisMonomials σ R).tensorProduct
    ((Finsupp.basisSingleOne : Module.Basis σ R (σ →₀ R)).exteriorPower n)

theorem basis_apply (n : ℕ) (d : σ →₀ ℕ) (s : Set.powersetCard σ n) :
    basis R σ n (d, s) = MvPolynomial.monomial d 1 ⊗ₜ[R]
      exteriorPower.ιMulti R n
        (fun j => Finsupp.single (Set.powersetCard.ofFinEmbEquiv.symm s j) 1) := by
  simp only [basis, Module.Basis.tensorProduct_apply, MvPolynomial.coe_basisMonomials,
    exteriorPower.basis_apply, exteriorPower.ιMulti_family, Finsupp.coe_basisSingleOne,
    Function.comp_def]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.FormMonomialBasis.PolynomialFormMonomialBasis
