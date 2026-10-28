import OAI.AlgebraicGeometry.Comparison.Betti.Open.ExteriorPresheaf
import OAI.AlgebraicGeometry.Comparison.Betti.Module.SheafificationRestriction

/-! # Open Sheaf -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Exterior.OpenSheaf

noncomputable section

/-! The actual exterior-form module sheaf commutes with native scheme restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) [IsOpenImmersion f.left]

def exteriorOpenSheafIso (n : ℕ) :
    (Scheme.Modules.restrictFunctor f.left).obj (ModuleSheaf.exteriorFormsModuleSheaf Y n) ≅
      ModuleSheaf.exteriorFormsModuleSheaf X n :=
  (Module.SheafificationRestriction.sheafificationRestrictionIso (Open.ExteriorPresheaf.openRestrictionRingHom f)
    (ModuleSheaf.exteriorFormsModulePresheaf Y n)).symm ≪≫
      (PresheafOfModules.sheafification.{0} (R := X.left.ringCatSheaf)
        (𝟙 X.left.ringCatSheaf.obj)).mapIso (Open.ExteriorPresheaf.exteriorOpenPresheafIso f n)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Exterior.OpenSheaf
