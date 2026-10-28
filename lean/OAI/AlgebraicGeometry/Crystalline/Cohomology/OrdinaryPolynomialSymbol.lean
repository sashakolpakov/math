import OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryPolynomialEq
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.FormMonomialBasis

/-! # Ordinary Polynomial Symbol -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryPolynomialSymbol.OrdinaryPolynomialSymbolExt

noncomputable section

/-! # Coordinate differential symbols determine linear maps on polynomial forms -/

universe u

variable (R σ : Type u) [CommRing R] [LinearOrder σ]
  (n : ℕ) {M : Type*} [AddCommGroup M] [Module R M]
  (f g : DeRhamPresentationTo.DeRhamPresentation.Form R (MvPolynomial σ R) n →ₗ[R] M)
  (h : ∀ a (v : Fin n → σ),
    f (DeRhamPresentationTo.DeRhamPresentation.symbol R (MvPolynomial σ R) a (MvPolynomial.X ∘ v)) =
      g (DeRhamPresentationTo.DeRhamPresentation.symbol R (MvPolynomial σ R) a (MvPolynomial.X ∘ v)))

include h in
theorem linearMap_ext : f = g := by
  let e := (OrdinaryPolynomialEq.OrdinaryPolynomialCoordinates.formsEquiv R σ n).restrictScalars R
  have he : f.comp e.toLinearMap = g.comp e.toLinearMap := by
    apply (Polynomial.FormMonomialBasis.PolynomialFormMonomialBasis.basis R σ n).ext
    rintro ⟨d, s⟩
    change f (e (Polynomial.FormMonomialBasis.PolynomialFormMonomialBasis.basis R σ n (d, s))) =
      g (e (Polynomial.FormMonomialBasis.PolynomialFormMonomialBasis.basis R σ n (d, s)))
    rw [Polynomial.FormMonomialBasis.PolynomialFormMonomialBasis.basis_apply]
    change f (OrdinaryPolynomialEq.OrdinaryPolynomialCoordinates.formsEquiv R σ n _) =
      g (OrdinaryPolynomialEq.OrdinaryPolynomialCoordinates.formsEquiv R σ n _)
    rw [OrdinaryPolynomialEq.OrdinaryPolynomialCoordinates.formsEquiv_word]
    exact h _ _
  apply LinearMap.ext
  intro ω
  obtain ⟨z, rfl⟩ := e.surjective ω
  exact DFunLike.congr_fun he z

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryPolynomialSymbol.OrdinaryPolynomialSymbolExt
