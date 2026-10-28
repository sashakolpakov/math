import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyFunctor

/-! # Cohomology Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.CohomologyRestriction

noncomputable section

/-! Restriction of coefficient scalars commutes with genuine sheaf cohomology. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

def coefficientCohomologyRestrictionIso
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    {X : Scheme.{u}} (c : S →+* Γ(X, ⊤)) (M : X.Modules) (q : ℕ) :
    (ModuleCat.restrictScalars.{u} f).obj
        ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c q).obj M) ≅
      (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (c.comp f) q).obj M :=
  ((ModuleCat.restrictScalarsComp.{u} f c).app
    ((Zariski.CohomologyFunctor.ZariskiCohomology.globalCohomologyFunctor X q).obj M)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.CohomologyRestriction
