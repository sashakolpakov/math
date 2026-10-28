import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.BaseForms

/-! # Base Form Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.BaseFormCoordinates

noncomputable section

/-! Principal base-form coordinates with the original divided-power ideal retained. -/

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (r : R) (δR : DividedPowers (Ideal.span {r})) (I : Ideal A) (δ : DividedPowers I)
  (hI : I = Ideal.span {algebraMap R A r})
  (hδ : DividedPowers.IsDPMorphism δR δ (algebraMap R A))

def formsEquiv (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ n ≃ₗ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n := by
  subst I
  exact BaseForms.formsEquiv R A r δR δ hδ n

theorem formsEquiv_symbol (n : ℕ) (a : A) (v : Fin n → A) :
    formsEquiv R A r δR I δ hI hδ n (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δ a v) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v := by
  subst I
  exact BaseForms.formsEquiv_symbol R A r δR δ hδ n a v

theorem differential (n : ℕ) (ω : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ n) :
    formsEquiv R A r δR I δ hI hδ (n + 1) (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential R A I δ n ω) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A n (formsEquiv R A r δR I δ hI hδ n ω) := by
  subst I
  exact BaseForms.differential R A r δR δ hδ n ω

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.BaseFormCoordinates
