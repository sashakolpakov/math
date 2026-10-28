import OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
import Mathlib.Basic.Complex.Basic

/-! # Module Presheaf -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Exterior.ModulePresheaf

noncomputable section

/-! Exterior forms on a presheaf of complex algebras retain their coefficient-module structure. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham

variable {C : Type*} [Category C] (F : Cᵒᵖ ⥤ CommAlgCat.{0} ℂ)

abbrev coefficientRings : Cᵒᵖ ⥤ RingCat.{0} :=
  F ⋙ forget₂ (CommAlgCat.{0} ℂ) CommRingCat ⋙ forget₂ CommRingCat RingCat

def formModule (U : Cᵒᵖ) (n : ℕ) : ModuleCat.{0} ((coefficientRings F).obj U) :=
  ModuleCat.of (F.obj U) (Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.Forms (F.obj U) n)

def formModuleMap {U V : Cᵒᵖ} (f : U ⟶ V) (n : ℕ) :
    formModule F U n ⟶
      (ModuleCat.restrictScalars ((coefficientRings F).map f).hom).obj (formModule F V n) :=
  ModuleCat.ofHom (R := (F.obj U)) (X := formModule F U n)
    (Y := (ModuleCat.restrictScalars ((coefficientRings F).map f).hom).obj (formModule F V n))
    { toFun := fun ω => Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap (F.map f) n ω
      map_add' := by intros; exact map_add _ _ _
      map_smul' a ω := Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap_smul (F.map f) n a ω }

def modulePresheaf (n : ℕ) : PresheafOfModules.{0} (coefficientRings F) where
  obj U := formModule F U n
  map f := formModuleMap F f n
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro ω
    change Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap (F.map (𝟙 U)) n ω = ω
    rw [F.map_id]
    exact Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap_id _ n ω
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro ω
    change Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap (F.map (f ≫ g)) n ω = Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap (F.map g) n (Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap (F.map f) n ω)
    rw [F.map_comp]
    exact Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap_comp _ _ n ω

end

end OAI.AlgebraicGeometry.Comparison.Betti.Exterior.ModulePresheaf
