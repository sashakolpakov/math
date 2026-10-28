import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyDegreeZero
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ModuleSectionIdentity

/-! # Degree Zero -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.DegreeZero.ZariskiCohomology

noncomputable section

/-! Degree-zero Ext cohomology identifies with actual global sections over every chosen coefficient ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def globalCohomologyZeroSectionsIso {X : Scheme.{u}} (M : X.Modules) :
    (Zariski.CohomologyFunctor.ZariskiCohomology.globalCohomologyFunctor X 0).obj M ≅ ModuleCat.of Γ(X, ⊤) Γ(M, ⊤) :=
  (Zariski.CohomologyDegreeZero.ZariskiCohomology.hZeroCanonicalLinearEquivGlobalSections M).toModuleIso

def coefficientCohomologyZeroSectionsEquiv {X : Scheme.{u}} {R : Type u} [CommRing R]
    (c : R →+* Γ(X, ⊤)) (M : X.Modules) :
    (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c 0).obj M ≃ₗ[R] (Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor c).obj M :=
  ((ModuleCat.restrictScalars c).mapIso (globalCohomologyZeroSectionsIso M)).toLinearEquiv.trans
    (Global.ModuleSectionIdentity.coefficientGlobalSectionsNativeIso c M).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.DegreeZero.ZariskiCohomology
