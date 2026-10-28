import OAI.AlgebraicGeometry.FormalGeometry.Completion.RelativeCechTerms

/-! # Relative Cech Faces -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.RelativeCechFaces.Construction

noncomputable section

/-! The actual relative Cech coface maps, with their literal restriction coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R))
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

/-- The native ordered coface map after canonical restriction of scalars to R. -/
def relativeStructureCechCoface (q : ℕ) (k : Fin (q + 2)) :
    (RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U).X q ⟶ (RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U).X (q + 1) :=
  (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of R)).inv.hom).map
    (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechCoface f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) U q k)

/-- Each coface coordinate is the actual section restriction from the deleted tuple. -/
theorem relativeStructureCechCoface_π (q : ℕ) (k : Fin (q + 2))
    (a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι (q + 1)) :
    relativeStructureCechCoface f U q k ≫ (RelativeCechTerms.Construction.relativeStructureCechTermIso f U (q + 1)).hom ≫
        Pi.π (RelativeCechTerms.Construction.relativeCechFactor f U (q + 1)) a =
      (RelativeCechTerms.Construction.relativeStructureCechTermIso f U q).hom ≫ Pi.π (RelativeCechTerms.Construction.relativeCechFactor f U q) (a.delete k) ≫
        (RelativeStructureSections.Construction.relativeStructureSections f).map
          (((FormalCoproduct.mk _ U).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ a.val).op := by
  rw [relativeStructureCechCoface, RelativeCechTerms.Construction.relativeStructureCechTermIso_hom_π,
    ← Category.assoc, ← Functor.map_comp, SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechCoface_comp_π,
    Functor.map_comp, Category.assoc]
  rw [RelativeCechTerms.Construction.relativeStructureCechTermIso_hom_π_assoc]
  apply congrArg (fun m =>
    (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of R)).inv.hom).map
      (Pi.π (fun b : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q =>
        SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) U q b.val) (a.delete k)) ≫ m)
  exact (RelativeStructureIntrinsic.Construction.relativeStructureSectionsNativeIso f).inv.naturality
    (((FormalCoproduct.mk _ U).mapPower (SimplexCategory.δ k).toOrderHom.toFun).φ a.val).op

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.RelativeCechFaces.Construction
