import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.ConstantSections

/-! # Presheaf Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Module.PresheafSections

noncomputable section

/-!
# IntegralComparison: elements give canonical constant-source presheaf sections
-/

open _root_.CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] (R : Type w) [CommRing R]
  (M : ModuleCat.{w} R) (P : C ⥤ ModuleCat.{w} R) (γ : (Functor.const C).obj M ⟶ P)

instance constant_linear : (Functor.const C : ModuleCat.{w} R ⥤ (C ⥤ ModuleCat.{w} R)).Linear R where
  map_smul := by intros; rfl

instance constant_additive : (Functor.const C : ModuleCat.{w} R ⥤ (C ⥤ ModuleCat.{w} R)).Additive where
  map_add := by intros; rfl

def sectionMap : M →ₗ[R] ((Functor.const C).obj (ModuleCat.of R R) ⟶ P) :=
  (Linear.rightComp R _ γ).comp
    (((Functor.const C).mapLinearMap R).comp (ConstantSections.elementHom R M).toLinearMap)

theorem sectionMap_apply (m : M) : sectionMap R M P γ m =
    (Functor.const C).map (ConstantSections.elementHom R M m) ≫ γ := rfl

theorem sectionMap_app_one (m : M) (U : C) :
    (sectionMap R M P γ m).app U (1 : R) = γ.app U m := by
  change γ.app U ((1 : R) • m) = γ.app U m
  rw [one_smul]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Module.PresheafSections
