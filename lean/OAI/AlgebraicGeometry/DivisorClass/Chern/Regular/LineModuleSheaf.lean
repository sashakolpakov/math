import OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.LineGluing
import OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.LineSectionModules

/-! # Line Module Sheaf -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.LineModuleSheaf

noncomputable section

/-! The glued regular sections form a native sheaf of modules on the original scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme} {ι : Type} (D : FunctionGluing.RegularLineCocycle X ι)

instance regularLineSection_ringModule (U : (Opens X)ᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U) (LineSections.RegularLineSection D U.unop) :=
  LineSectionModules.regularLineSection_module D U.unop

def regularLineModulePresheaf : PresheafOfModules X.ringCatSheaf.obj where
  obj U := ModuleCat.of _ (LineSections.RegularLineSection D U.unop)
  map {U V} f := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map f).hom).obj
      (ModuleCat.of _ (LineSections.RegularLineSection D V.unop)))
    { toFun := LineSections.regularLineSectionRestrict D (leOfHom f.unop)
      map_add' := (LineSections.regularLineSectionRestrict D (leOfHom f.unop)).map_add
      map_smul' := LineSectionModules.regularLineSectionRestrict_smul D (leOfHom f.unop) }
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    rfl

theorem regularLineModulePresheaf_isSheaf : Presheaf.IsSheaf (Opens.grothendieckTopology X)
    (regularLineModulePresheaf D).presheaf := LineGluing.regularLineSectionPresheaf_isSheaf D

def regularLineModuleSheaf : X.Modules where
  val := regularLineModulePresheaf D
  isSheaf := regularLineModulePresheaf_isSheaf D

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.LineModuleSheaf
