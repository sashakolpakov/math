import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.FinitenessProperty

/-! # Additivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology

noncomputable section

/-! Canonical coefficient cohomology is additive, sends zero objects to zero, and preserves finiteness under sheaf isomorphisms. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

instance Additivity.ZariskiCohomology.coefficientCohomologyFunctor_additive {X : Scheme.{u}} {R : Type u} [CommRing R]
    (c : R →+* Γ(X, ⊤)) (n : ℕ) : (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c n).Additive := by
  change (Zariski.CohomologyFunctor.ZariskiCohomology.globalCohomologyFunctor X n ⋙ ModuleCat.restrictScalars c).Additive
  infer_instance

variable {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤))

theorem FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite.of_isZero (M : X.Modules) (hM : IsZero M) : FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite c M := by
  intro n
  have : Subsingleton ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c n).obj M) :=
    ModuleCat.subsingleton_of_isZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c n).map_isZero hM)
  infer_instance

theorem FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite.of_iso {M N : X.Modules} (e : M ≅ N) (hM : FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite c M) :
    FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite c N := by
  intro n
  have : Module.Finite R ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c n).obj M) := hM n
  exact Module.Finite.equiv ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c n).mapIso e).toLinearEquiv

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology
