import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.DegreeZero

/-! # Finiteness Property -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.FinitenessProperty.ZariskiCohomology

noncomputable section

/-! Finiteness of genuine cohomology in all degrees with its fixed coefficient action. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

def CoefficientCohomologyFinite {X : Scheme.{u}} {R : Type u} [CommRing R]
    (c : R →+* Γ(X, ⊤)) : ObjectProperty X.Modules :=
  fun M ↦ ∀ q : ℕ, Module.Finite R ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c q).obj M)

theorem coefficientCohomologyFinite_of_sections_and_vanishing
    {X : Scheme.{u}} {R : Type u} [CommRing R]
    (c : R →+* Γ(X, ⊤)) (M : X.Modules)
    (hΓ : Module.Finite R ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor c).obj M))
    (hH : ∀ q : ℕ, Subsingleton (Zariski.Cohomology.ZariskiCohomology.H M (q + 1))) : CoefficientCohomologyFinite c M := by
  intro q
  cases q with
  | zero =>
      exact @Module.Finite.equiv R _ _ _ _ _ _ _ hΓ (DegreeZero.ZariskiCohomology.coefficientCohomologyZeroSectionsEquiv c M).symm
  | succ q =>
      have : Subsingleton ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (q + 1)).obj M) := hH q
      infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.FinitenessProperty.ZariskiCohomology
