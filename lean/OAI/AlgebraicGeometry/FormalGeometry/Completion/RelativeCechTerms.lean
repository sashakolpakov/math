import OAI.AlgebraicGeometry.FormalGeometry.Completion.RelativeCechZeroCycles
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Relative Cech Terms -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.RelativeCechTerms.Construction

noncomputable section

/-! The actual literal-base Cech terms are products of the actual chart section modules. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R))
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

abbrev relativeCechFactor (q : ℕ) (a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q) : ModuleCat.{u} R :=
  (RelativeStructureSections.Construction.relativeStructureSections f).obj (op (∏ᶜ fun k : Fin (q + 1) => U (a.val k)))

/-- The termwise product identification uses the native scalar-restriction comparison. -/
def relativeStructureCechTermIso (q : ℕ) :
    (RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U).X q ≅ ∏ᶜ (relativeCechFactor f U q) :=
  PreservesProduct.iso (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of R)).inv.hom)
    (fun a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) U q a.val) ≪≫
      Pi.mapIso (fun a => ((RelativeStructureIntrinsic.Construction.relativeStructureSectionsNativeIso f).app
        (op (∏ᶜ fun k : Fin (q + 1) => U (a.val k)))).symm)

@[reassoc]
theorem relativeStructureCechTermIso_hom_π (q : ℕ) (a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q) :
    (relativeStructureCechTermIso f U q).hom ≫ Pi.π (relativeCechFactor f U q) a =
      (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of R)).inv.hom).map
        (Pi.π (fun b : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q =>
          SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) U q b.val) a) ≫
        ((RelativeStructureIntrinsic.Construction.relativeStructureSectionsNativeIso f).app
          (op (∏ᶜ fun k : Fin (q + 1) => U (a.val k)))).inv := by
  rw [relativeStructureCechTermIso, Iso.trans_hom, Category.assoc, Pi.mapIso_hom_π,
    ← Category.assoc, PreservesProduct.iso_hom, piComparison_comp_π]
  rfl

theorem relativeStructureCechTermIso_coordinate (q : ℕ)
    (x : (RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U).X q) (a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q) :
    Pi.π (relativeCechFactor f U q) a ((relativeStructureCechTermIso f U q).hom x) =
      Pi.π (fun b : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q =>
        SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) U q b.val) a x :=
  ConcreteCategory.congr_hom (relativeStructureCechTermIso_hom_π f U q a) x

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.RelativeCechTerms.Construction
