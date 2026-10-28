import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.ComplexRestriction

/-! # Restriction Augmentation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.RestrictionAugmentation

noncomputable section

/-!
# IntegralComparison: restriction of the relative crystalline complex preserves its structure-presheaf augmentation
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

universe u v w v' w'

variable {C : Type v} [Category.{w} C] {D : Type v'} [Category.{w'} D]
  {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} (t : D ⥤ C)
  (H Q : C ⥤ BigCrystallineSite.Object p B J δ f) (π : H ⟶ Q)

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.ComplexRestriction.restriction (B := B) t
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.ModuleComplex.ambientPresheaf Q

def sourceIso : ((F).mapHomologicalComplex (ComplexShape.up ℕ)).obj ((CochainComplex.single₀ _).obj A) ≅
    (CochainComplex.single₀ _).obj (RelativeCrystalline.ModuleComplex.ambientPresheaf (t ⋙ Q)) :=
  (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℕ) 0).app A

theorem sourceIso_inv_zero : (sourceIso t Q).inv.f 0 = 𝟙 ((F).obj A) :=
  (HomologicalComplex.singleMapHomologicalComplex_inv_app_self F (ComplexShape.up ℕ) 0 A).trans
    (by
      simp only [CochainComplex.single₀ObjXSelf, Iso.refl_hom, Iso.refl_inv]
      change 𝟙 ((F).obj A) ≫ (F).map (𝟙 A) = 𝟙 ((F).obj A)
      rw [(F).map_id, Category.id_comp])

def mappedAugmentation :
    (CochainComplex.single₀ _).obj (RelativeCrystalline.ModuleComplex.ambientPresheaf (t ⋙ Q)) ⟶
      ((F).mapHomologicalComplex (ComplexShape.up ℕ)).obj (RelativeCrystalline.ModuleComplex.complex H Q π) :=
  (sourceIso t Q).inv ≫ ((F).mapHomologicalComplex (ComplexShape.up ℕ)).map
    (RelativeCrystalline.ModuleComplex.augmentation H Q π)

theorem mappedAugmentation_zero : (mappedAugmentation t H Q π).f 0 =
    (F).map (RelativeCrystalline.ModuleComplex.augmentationZero H Q π) := by
  change (sourceIso t Q).inv.f 0 ≫ (F).map ((RelativeCrystalline.ModuleComplex.augmentation H Q π).f 0) = _
  exact (congrArg (fun β => β ≫ (F).map ((RelativeCrystalline.ModuleComplex.augmentation H Q π).f 0))
    (sourceIso_inv_zero t Q)).trans
      ((Category.id_comp _).trans
        (congrArg (F).map (RelativeCrystalline.ModuleComplex.augmentation_zero H Q π)))

theorem augmentationZero : (F).map (RelativeCrystalline.ModuleComplex.augmentationZero H Q π) ≫
    (ComplexRestriction.formsIso t H Q π 0).hom =
      RelativeCrystalline.ModuleComplex.augmentationZero (t ⋙ H) (t ⋙ Q) (Functor.whiskerLeft t π) := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  rfl

theorem augmentation : mappedAugmentation t H Q π ≫ (ComplexRestriction.complexIso t H Q π).hom =
    RelativeCrystalline.ModuleComplex.augmentation (t ⋙ H) (t ⋙ Q) (Functor.whiskerLeft t π) := by
  apply (CochainComplex.fromSingle₀Equiv
    (RelativeCrystalline.ModuleComplex.complex (t ⋙ H) (t ⋙ Q) (Functor.whiskerLeft t π))
    (RelativeCrystalline.ModuleComplex.ambientPresheaf (t ⋙ Q))).injective
  apply Subtype.ext
  change (mappedAugmentation t H Q π).f 0 ≫ (ComplexRestriction.formsIso t H Q π 0).hom =
    (RelativeCrystalline.ModuleComplex.augmentation (t ⋙ H) (t ⋙ Q) (Functor.whiskerLeft t π)).f 0
  exact (congrArg (fun β => β ≫ (ComplexRestriction.formsIso t H Q π 0).hom)
    (mappedAugmentation_zero t H Q π)).trans
      ((augmentationZero t H Q π).trans
        (RelativeCrystalline.ModuleComplex.augmentation_zero (t ⋙ H) (t ⋙ Q) (Functor.whiskerLeft t π)).symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.RestrictionAugmentation
