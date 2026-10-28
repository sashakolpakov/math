import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.DegreeZeroComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.HomologyScalars

/-! # Degree Zero Linearity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.DegreeZeroLinearity

noncomputable section

/-! The degree-zero Cech comparison respects the original coefficient action on sections and homology. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry
universe u

def coefficientCechZeroSectionsModuleIso
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤))
    (M : X.Modules) {ι : Type u} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) :
    (Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor c).obj M ≅ (Intrinsic.CoefficientCechComplex.coefficientCechComplex c M U).homology 0 := by
  refine ModuleCat.isoMk (DegreeZeroComparison.coefficientCechZeroSectionsAddIso c M U hU) ?_
  intro r
  apply ConcreteCategory.hom_ext
  intro x
  have h := ConcreteCategory.congr_hom
    (DegreeZeroComparison.coefficientCechZeroSectionsAddIso_naturality c (Global.ModuleScalars.globalModuleScalar M (c r)) U hU) x
  have ht := ConcreteCategory.congr_hom
    (HomologyScalars.coefficientCech_globalScalar_homologyMap c M U r 0)
    ((DegreeZeroComparison.coefficientCechZeroSectionsAddIso c M U hU).hom x)
  exact (h.trans ht).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.DegreeZeroLinearity
