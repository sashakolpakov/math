import OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryPolynomialEq
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Frame Linearization -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.FrameLinearization.PolynomialFrameLinearization

noncomputable section

/-!
# Actual scalar extensions of ordinary polynomial forms

For every algebra over a polynomial frame, extending the ordinary form
module to the ambient algebra gives precisely the coordinate tensor term.
The comparison sends ordinary coordinate symbols to their actual coordinate
wedges. This identifies the terms used in frame linearization.
-/

open scoped TensorProduct

universe u

variable (R σ A : Type u) [CommRing R] [CommRing A] [LinearOrder σ]
  [Algebra R A] [Algebra (MvPolynomial σ R) A] [IsScalarTower R (MvPolynomial σ R) A]

local notation "P" => MvPolynomial σ R

def termEquiv (n : ℕ) :
    (A ⊗[P] DeRhamPresentationTo.DeRhamPresentation.Form R P n) ≃ₗ[A] Koszul.Tensor.KoszulTensor.Term R σ A n :=
  ((OrdinaryPolynomialEq.OrdinaryPolynomialCoordinates.formsEquiv R σ n).symm.baseChange P A _ _).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R P A A (⋀[R]^n (σ →₀ R)))

theorem termEquiv_symbol (n : ℕ) (a : A) (b : P) (v : Fin n → σ) :
    termEquiv R σ A n (a ⊗ₜ[P] DeRhamPresentationTo.DeRhamPresentation.symbol R P b (MvPolynomial.X ∘ v)) =
      (b • a) ⊗ₜ[R] exteriorPower.ιMulti R n (fun i => Finsupp.single (v i) 1) := by
  have hv : (OrdinaryPolynomialEq.OrdinaryPolynomialCoordinates.formsEquiv R σ n).symm
      (DeRhamPresentationTo.DeRhamPresentation.symbol R P b (MvPolynomial.X ∘ v)) =
        b ⊗ₜ[R] exteriorPower.ιMulti R n (fun i => Finsupp.single (v i) 1) :=
    ((OrdinaryPolynomialEq.OrdinaryPolynomialCoordinates.formsEquiv R σ n).symm_apply_eq).mpr
      (OrdinaryPolynomialEq.OrdinaryPolynomialCoordinates.formsEquiv_word R σ n b v).symm
  change TensorProduct.AlgebraTensorModule.cancelBaseChange R P A A (⋀[R]^n (σ →₀ R))
    (((OrdinaryPolynomialEq.OrdinaryPolynomialCoordinates.formsEquiv R σ n).symm.baseChange P A _ _)
      (a ⊗ₜ[P] DeRhamPresentationTo.DeRhamPresentation.symbol R P b (MvPolynomial.X ∘ v))) = _
  rw [LinearEquiv.baseChange_tmul, hv, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]

theorem termEquiv_symm_word (n : ℕ) (a : A) (v : Fin n → σ) :
    (termEquiv R σ A n).symm (a ⊗ₜ[R] exteriorPower.ιMulti R n (fun i => Finsupp.single (v i) 1)) =
      a ⊗ₜ[P] DeRhamPresentationTo.DeRhamPresentation.symbol R P 1 (MvPolynomial.X ∘ v) := by
  apply (termEquiv R σ A n).injective
  rw [LinearEquiv.apply_symm_apply, termEquiv_symbol, one_smul]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.FrameLinearization.PolynomialFrameLinearization
