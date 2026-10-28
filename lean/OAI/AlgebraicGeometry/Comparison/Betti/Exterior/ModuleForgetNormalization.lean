import OAI.AlgebraicGeometry.Comparison.Betti.Exterior.ModuleForget
import OAI.AlgebraicGeometry.Comparison.Betti.ForgetSheafification

/-! # Module Forget Normalization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Exterior.ModuleForgetNormalization

noncomputable section

section

/-! The preserved exterior-form sheaf adapter is normalized on the original
algebraic symbols and their actual sheafification unit. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)

theorem exteriorFormSheafIso_hom (n : ℕ) :
    (Forms.exteriorFormSheafIso X n).hom =
      (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).map
        (Forms.exteriorFormPresheafIso X n).hom := by
  change (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).map
      (NumberTheory.PadicHodge.GeometricComparison.SheafFormsAdapter.FormsAdapter.formPresheafIso X n).hom ≫
    (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).map
      (Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.formsPresheafIso ℂ X n).hom = _
  exact (Functor.map_comp _ _ _).symm

theorem exteriorFormSheafIso_inv (n : ℕ) :
    (Forms.exteriorFormSheafIso X n).inv =
      (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).map
        (Forms.exteriorFormPresheafIso X n).inv := by
  have he : Forms.exteriorFormSheafIso X n =
      (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).mapIso
        (Forms.exteriorFormPresheafIso X n) := Iso.ext (exteriorFormSheafIso_hom X n)
  exact congrArg Iso.inv he

theorem exteriorFormSheafIso_unit (n : ℕ) :
    toSheafify (Opens.grothendieckTopology X.left) (Algebraic.Sheaves.formPresheaf X n) ≫
      (Forms.exteriorFormSheafIso X n).hom.hom =
        (Forms.exteriorFormPresheafIso X n).hom ≫
          toSheafify (Opens.grothendieckTopology X.left)
            (Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsPresheaf ℂ X n) := by
  rw [exteriorFormSheafIso_hom]
  exact (toSheafify_naturality _ _).symm

end

/-! Exact normalization of the original module-forgetting isomorphism on
the algebraic presheaf before sheafification. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)

theorem exteriorFormsModuleSheafForgetIso_unit (n : ℕ) :
    toSheafify (Opens.grothendieckTopology X.left)
        (ModuleSheaf.exteriorFormsModulePresheaf X n).presheaf ≫
      (ModuleForget.exteriorFormsModuleSheafForgetIso X n).hom.hom =
    (ModuleSheaf.exteriorFormsModulePresheafForgetIso X n).hom ≫
      Functor.whiskerRight (Forms.exteriorFormPresheafIso X n).inv
        (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}) ≫
      Functor.whiskerRight
        (toSheafify (Opens.grothendieckTopology X.left) (Algebraic.Sheaves.formPresheaf X n))
        (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}) := by
  let J := Opens.grothendieckTopology X.left
  let G := forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}
  change toSheafify J (ModuleSheaf.exteriorFormsModulePresheaf X n).presheaf ≫
      ((presheafToSheaf J AddCommGrpCat).map
        (ModuleSheaf.exteriorFormsModulePresheafForgetIso X n).hom).hom ≫
      (ModuleForget.exteriorPresheafSheafificationForgetIso X n).hom.hom ≫
      Functor.whiskerRight (Forms.exteriorFormSheafIso X n).inv.hom G = _
  rw [← toSheafify_naturality_assoc]
  have h := ForgetSheafification.complexAdditiveSheafificationIso_unit (TopCat.of X.left)
    (Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsPresheaf ℂ X n)
  change toSheafify J
      (Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsPresheaf ℂ X n ⋙ G) ≫
      (ModuleForget.exteriorPresheafSheafificationForgetIso X n).hom.hom = _ at h
  erw [← Category.assoc
    (toSheafify J (Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsPresheaf ℂ X n ⋙ G))
    (ModuleForget.exteriorPresheafSheafificationForgetIso X n).hom.hom _, h]
  erw [exteriorFormSheafIso_inv, ← Functor.whiskerRight_comp]
  erw [← toSheafify_naturality, Functor.whiskerRight_comp]
  rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Exterior.ModuleForgetNormalization
