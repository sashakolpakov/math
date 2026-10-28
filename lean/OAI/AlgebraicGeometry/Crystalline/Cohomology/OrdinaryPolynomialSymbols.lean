import OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryPolynomialEq

/-! # Ordinary Polynomial Symbols -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryPolynomialSymbols.OrdinaryPolynomialCoordinateSymbols

noncomputable section

/-! # The canonical polynomial complex isomorphism on coordinate symbols -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable (R σ : Type u) [CommRing R] [Fintype σ]

local notation "P" => MvPolynomial σ R

theorem hom_word (n : ℕ) (a : P) (v : Fin n → σ) :
    (OrdinaryPolynomialEq.OrdinaryPolynomialCoordinates.complexIso R σ).hom.f n
      (a ⊗ₜ[R] exteriorPower.ιMulti R n (fun i => Finsupp.single (v i) 1)) =
        DeRhamPresentationTo.DeRhamPresentation.symbol R P a (MvPolynomial.X ∘ v) := by
  change ZeroIdeal.ZeroIdealPDForms.formsEquiv R P n
    (PD.FormsTensor.PDFormsTensor.toForms R P σ (⊥ : Ideal P) (dividedPowersBot P) MvPolynomial.X n _) = _
  rw [PD.FormsTensor.PDFormsTensor.toForms_word, ZeroIdeal.ZeroIdealPDForms.formsEquiv_symbol]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryPolynomialSymbols.OrdinaryPolynomialCoordinateSymbols
