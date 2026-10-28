import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.DegreeZeroLinearity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.ZariskiComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.DegreeZero

/-! # All Degree Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.AllDegreeComparison

noncomputable section

/-! The finite ordered coefficient Cech complex computes actual global sections in degree zero and genuine coefficient cohomology in every degree. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry
universe u

def orderedCechZeroSectionsModuleIso
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤))
    (M : X.Modules) {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (hU : ⨆ i, U i = ⊤) :
    (Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor c).obj M ≅ (Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c M U).homology 0 :=
  CoefficientCech.DegreeZeroLinearity.coefficientCechZeroSectionsModuleIso c M U hU ≪≫ Ordered.CoefficientCechHomotopyEquivalence.coefficientCechOrderedHomologyIso c M U 0

def orderedCechCohomologyModuleIso
    {X : Scheme.{u}} [X.IsSeparated] {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤))
    (M : X.Modules) [M.IsQuasicoherent] {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) (ha : ∀ i, IsAffineOpen (U i)) (n : ℕ) :
    (Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c M U).homology n ≅
      (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c n).obj M := by
  cases n with
  | zero =>
      exact (orderedCechZeroSectionsModuleIso c M U hU).symm ≪≫
        (CoefficientCohomology.DegreeZero.ZariskiCohomology.coefficientCohomologyZeroSectionsEquiv c M).symm.toModuleIso
  | succ n => exact ZariskiComparison.orderedCechZariskiModuleIso c M U hU ha n

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.AllDegreeComparison
