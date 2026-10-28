import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.RestrictionCompatibility

/-! # Module Presheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.ModulePresheaf

noncomputable section

/-! Compatible frame-coordinate modules and their restriction maps form an actual presheaf of modules on the scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (D : Transitions.OpenFrameTransitions U)

def openFrameModulePresheaf : PresheafOfModules X.ringCatSheaf.obj where
  obj V := ModuleCat.of Γ(X, V.unop) (SectionModules.openFrameSectionModule U D V.unop)
  map {V W} h := ModuleCat.ofHom
    (X := ModuleCat.of Γ(X, V.unop) (SectionModules.openFrameSectionModule U D V.unop))
    (Y := (ModuleCat.restrictScalars (X.presheaf.map h).hom).obj
      (ModuleCat.of Γ(X, W.unop) (SectionModules.openFrameSectionModule U D W.unop))) {
      __ := (RestrictionCompatibility.openFrameSectionRestriction D h.unop.le).toAddMonoidHom
      map_smul' := (RestrictionCompatibility.openFrameSectionRestriction D h.unop.le).map_smul' }
  map_id V := by
    apply ModuleCat.hom_ext
    ext x
    exact RestrictionCompatibility.openFrameSectionRestriction_refl D V.unop x
  map_comp {V W Z} h k := by
    apply ModuleCat.hom_ext
    ext x
    exact (RestrictionCompatibility.openFrameSectionRestriction_comp D h.unop.le k.unop.le x).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.ModulePresheaf
