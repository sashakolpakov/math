import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.FormsBaseQuotient
import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.FormsBaseExtension

/-! # Ordinary Base Quotient -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryBaseQuotient.Ordinary

noncomputable section

/-! Canonical ordinary differential-form coordinates after quotienting the coefficient base. -/

open _root_.CategoryTheory

universe u

variable (R S A : Type u) [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]
  (h : Function.Surjective (algebraMap R S))

def formsEquiv (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n ≃ₗ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form S A n :=
  Submodule.quotEquivOfEq _ _ (PD.FormsBaseQuotient.ordinaryRelations_eq R S A h n)

theorem formsEquiv_symbol (n : ℕ) (a : A) (v : Fin n → A) :
    formsEquiv R S A h n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol S A a v :=
  Submodule.quotEquivOfEq_mk _ _ _ _

theorem formsEquiv_eq (n : ℕ) : (formsEquiv R S A h n).toLinearMap =
    PD.FormsBaseExtension.ordinaryMap R S A n := by
  apply LinearMap.ext
  intro ω
  obtain ⟨a, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A n).mkQ_surjective ω
  exact Submodule.quotEquivOfEq_mk _ _ _ _

theorem differential (n : ℕ) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) :
    formsEquiv R S A h (n + 1) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A n ω) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential S A n (formsEquiv R S A h n ω) := by
  change (formsEquiv R S A h (n + 1)).toLinearMap _ =
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential S A n ((formsEquiv R S A h n).toLinearMap _)
  rw [formsEquiv_eq, formsEquiv_eq]
  exact PD.FormsBaseExtension.ordinaryMap_differential R S A n ω

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryBaseQuotient.Ordinary
