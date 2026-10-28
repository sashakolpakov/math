import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.Additivity

/-! # Isomorphism Property -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.IsomorphismProperty

noncomputable section

/-! Finiteness of genuine coefficient cohomology is invariant under actual sheaf isomorphisms. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules
universe u
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.Additivity.ZariskiCohomology

instance coefficientCohomologyFinite_closedUnderIsomorphisms
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) :
    (FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite c).IsClosedUnderIsomorphisms where
  of_iso e h := FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite.of_iso c e h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.IsomorphismProperty
