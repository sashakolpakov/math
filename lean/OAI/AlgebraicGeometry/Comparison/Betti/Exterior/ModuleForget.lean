import OAI.AlgebraicGeometry.Comparison.Betti.Exterior.ModuleSheaf
import OAI.AlgebraicGeometry.Comparison.Betti.ForgetSheafification

/-! # Module Forget -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Exterior.ModuleForget

noncomputable section

/-! Forgetting the structure-sheaf module action recovers the original algebraic form sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)

def exteriorModuleSheafificationForgetIso (n : ℕ) :
    (SheafOfModules.toSheaf.{0} X.left.ringCatSheaf).obj (ModuleSheaf.exteriorFormsModuleSheaf X n) ≅
      (presheafToSheaf (Opens.grothendieckTopology X.left) AddCommGrpCat.{0}).obj
        (ModuleSheaf.exteriorFormsModulePresheaf X n).presheaf :=
  (PresheafOfModules.sheafificationCompToSheaf.{0} (𝟙 X.left.ringCatSheaf.obj)).app
    (ModuleSheaf.exteriorFormsModulePresheaf X n)

def exteriorPresheafSheafificationForgetIso (n : ℕ) :
    (presheafToSheaf (Opens.grothendieckTopology X.left) AddCommGrpCat.{0}).obj
        (Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsPresheaf ℂ X n ⋙
          forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}) ≅
      (sheafCompose (Opens.grothendieckTopology X.left)
        (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj
          (Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsSheaf ℂ X n) :=
  (ForgetSheafification.complexAdditiveSheafificationIso (TopCat.of X.left)).app
      (Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsPresheaf ℂ X n)

def exteriorFormsModuleSheafForgetIso (n : ℕ) :
    (SheafOfModules.toSheaf.{0} X.left.ringCatSheaf).obj (ModuleSheaf.exteriorFormsModuleSheaf X n) ≅
      (sheafCompose (Opens.grothendieckTopology X.left)
        (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat)).obj ((Algebraic.Sheaves.algebraicDeRhamSheafComplex X).X n) :=
  exteriorModuleSheafificationForgetIso X n ≪≫
    (presheafToSheaf (Opens.grothendieckTopology X.left) AddCommGrpCat).mapIso
      (ModuleSheaf.exteriorFormsModulePresheafForgetIso X n) ≪≫
    exteriorPresheafSheafificationForgetIso X n ≪≫
    (sheafCompose (Opens.grothendieckTopology X.left)
      (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat)).mapIso (Forms.exteriorFormSheafIso X n).symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.Exterior.ModuleForget
