import OAI.AlgebraicGeometry.FormalGeometry.Completion.RelativeStructureSections

/-! # Relative Structure Intrinsic -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.RelativeStructureIntrinsic.Construction

noncomputable section

/-! The compact literal-base structure presheaf agrees with the native scheme-module presheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R))

/-- The actual structure presheaf is the native base-module presheaf after canonical scalar restriction. -/
def relativeStructureSectionsNativeIso :
    RelativeStructureSections.Construction.relativeStructureSections f ≅
      SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) ⋙
        ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of R)).inv.hom :=
  NatIso.ofComponents (fun _ => ModuleCat.isoMk (Iso.refl _) (by
    intro r
    ext s
    rfl)) (by
    intro U V i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    rfl)

theorem relativeStructureSectionsNativeIso_apply (U : X.Opens)
    (s : (RelativeStructureSections.Construction.relativeStructureSections f).obj (op U)) :
    (relativeStructureSectionsNativeIso f).hom.app (op U) s = s := rfl

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.RelativeStructureIntrinsic.Construction
