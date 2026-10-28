import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.Augmentation

/-! # Section Cycle Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.SectionCycleValues

noncomputable section

/-! The canonical ordered zero-cycle of a section has exactly its restricted section values. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u

theorem orderedCechSectionToCycles_π {X : Scheme.{u}} {R : Type u} [CommRing R]
    (c : R →+* Γ(X, ⊤)) (M : X.Modules) {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) (x : (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).obj (op ⊤))
    (a : Ordered.SectionCechIndices.OrderedCechIndex ι 0) :
    Pi.π (fun j : Ordered.SectionCechIndices.OrderedCechIndex ι 0 => Ordered.CoefficientCechTerms.coefficientCechFactor c M U 0 j.1) a
      (Augmentation.orderedCechSectionToCycles c M U x).val =
      M.presheaf.map (∏ᶜ fun k => U (a.1 k)).leTop.op x :=
  ConcreteCategory.congr_hom (Augmentation.orderedCechSectionMap_comp_π c M U 0 a) x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.SectionCycleValues
