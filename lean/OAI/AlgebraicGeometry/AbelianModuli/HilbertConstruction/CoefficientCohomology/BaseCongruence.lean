import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.GlobalSectionsPushforward

/-! # Base Congruence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.BaseCongruence.ZariskiCohomology

noncomputable section

/-! Equal structural coefficient maps induce the same actual coefficient cohomology object. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

def coefficientCohomologyCongr {X : Scheme.{u}} {R : Type u} [CommRing R]
    {c d : R →+* Γ(X, ⊤)} (h : c = d) (M : X.Modules) (n : ℕ) :
    (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c n).obj M ≅ (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor d n).obj M :=
  eqToIso (congrArg (fun z => (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor z n).obj M) h)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.BaseCongruence.ZariskiCohomology
