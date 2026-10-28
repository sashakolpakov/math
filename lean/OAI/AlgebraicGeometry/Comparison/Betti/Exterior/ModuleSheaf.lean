import OAI.AlgebraicGeometry.Comparison.Betti.Exterior.Forms
import OAI.AlgebraicGeometry.Comparison.Betti.Exterior.ModulePresheaf
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Module Sheaf -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Exterior.ModuleSheaf

noncomputable section

/-! The actual exterior forms, with their structure-sheaf module actions retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)

def sectionCoefficientRingsIso : X.left.ringCatSheaf.obj ≅
    ModulePresheaf.coefficientRings (Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras ℂ X) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro U V f
    ext a
    rfl)

def exteriorFormsModulePresheaf (n : ℕ) : X.left.PresheafOfModules :=
  (PresheafOfModules.restrictScalars (sectionCoefficientRingsIso X).hom).obj
    (ModulePresheaf.modulePresheaf (Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras ℂ X) n)

def exteriorFormsModuleSheaf (n : ℕ) : X.left.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.left.ringCatSheaf.obj)).obj (exteriorFormsModulePresheaf X n)

def exteriorFormsModulePresheafForgetIso (n : ℕ) :
    (exteriorFormsModulePresheaf X n).presheaf ≅
      Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsPresheaf ℂ X n ⋙ forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro U V f
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro ω
    rfl)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Exterior.ModuleSheaf
