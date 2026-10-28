import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.PostcomposeComplex

/-! # Postcompose Augmentation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.PostcomposeAugmentation

noncomputable section

/-!
# IntegralComparison: geometric postcomposition preserves the original relative augmentation
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

universe u v w

variable {C : Type v} [Category.{w} C] {p : ℕ} {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (hg : g ≫ fY = f) (H Q : C ⥤ BigCrystallineSite.Object p B J δ f) (π : H ⟶ Q)

def sourceIso : (CochainComplex.single₀ _).obj
    (RelativeCrystalline.ModuleComplex.ambientPresheaf (Q ⋙ BigCrystallineSite.postcompose g hg)) ≅
      (CochainComplex.single₀ _).obj (RelativeCrystalline.ModuleComplex.ambientPresheaf Q) := Iso.refl _

theorem augmentationZero : RelativeCrystalline.ModuleComplex.augmentationZero
    (H ⋙ BigCrystallineSite.postcompose g hg) (Q ⋙ BigCrystallineSite.postcompose g hg) (Functor.whiskerRight π (BigCrystallineSite.postcompose g hg)) =
      RelativeCrystalline.ModuleComplex.augmentationZero H Q π := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  rfl

def sourceAugmentation : (CochainComplex.single₀ _).obj
    (RelativeCrystalline.ModuleComplex.ambientPresheaf (Q ⋙ BigCrystallineSite.postcompose g hg)) ⟶
      RelativeCrystalline.ModuleComplex.complex (H ⋙ BigCrystallineSite.postcompose g hg) (Q ⋙ BigCrystallineSite.postcompose g hg)
        (Functor.whiskerRight π (BigCrystallineSite.postcompose g hg)) :=
  RelativeCrystalline.ModuleComplex.augmentation (H ⋙ BigCrystallineSite.postcompose g hg) (Q ⋙ BigCrystallineSite.postcompose g hg)
    (Functor.whiskerRight π (BigCrystallineSite.postcompose g hg))

def targetAugmentation : (CochainComplex.single₀ _).obj
    (RelativeCrystalline.ModuleComplex.ambientPresheaf Q) ⟶ RelativeCrystalline.ModuleComplex.complex H Q π :=
  RelativeCrystalline.ModuleComplex.augmentation H Q π

theorem sourceAugmentation_zero : (sourceAugmentation g hg H Q π).f 0 =
    RelativeCrystalline.ModuleComplex.augmentationZero
      (H ⋙ BigCrystallineSite.postcompose g hg) (Q ⋙ BigCrystallineSite.postcompose g hg) (Functor.whiskerRight π (BigCrystallineSite.postcompose g hg)) :=
  RelativeCrystalline.ModuleComplex.augmentation_zero
    (H ⋙ BigCrystallineSite.postcompose g hg) (Q ⋙ BigCrystallineSite.postcompose g hg) (Functor.whiskerRight π (BigCrystallineSite.postcompose g hg))

theorem targetAugmentation_zero : (targetAugmentation H Q π).f 0 =
    RelativeCrystalline.ModuleComplex.augmentationZero H Q π :=
  RelativeCrystalline.ModuleComplex.augmentation_zero H Q π

theorem component_zero (U : Cᵒᵖ) (a : (Q.obj U.unop).ring) :
    ((sourceAugmentation g hg H Q π).f 0).app U a = ((targetAugmentation H Q π).f 0).app U a := by
  have h₁ := congrArg (fun β => β.app U a) (sourceAugmentation_zero g hg H Q π)
  have h₂ := congrArg (fun β => β.app U a) (augmentationZero g hg H Q π)
  have h₃ := congrArg (fun β => β.app U a) (targetAugmentation_zero H Q π)
  exact h₁.trans (h₂.trans h₃.symm)

theorem augmentation : sourceAugmentation g hg H Q π ≫
      (PostcomposeComplex.complexIso g hg H Q π).hom =
    (sourceIso g hg Q).hom ≫ targetAugmentation H Q π := by
  apply (CochainComplex.fromSingle₀Equiv (RelativeCrystalline.ModuleComplex.complex H Q π)
    (RelativeCrystalline.ModuleComplex.ambientPresheaf (Q ⋙ BigCrystallineSite.postcompose g hg))).injective
  apply Subtype.ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact component_zero g hg H Q π U a

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.PostcomposeAugmentation
