import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.PresentedMapFullness

/-! # Presented Map Composition -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.PresentedMapComposition

noncomputable section

/-!
# Composition and pullback of morphisms in affine presentations
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

section

open OAI.AlgebraicGeometry.Picard.PoincareBundle.PresentedMapNaturality

variable {C D : Type*} [Category C] [Category D]

theorem recover_from_square (F : C ⥤ D) {M N : C} {X Y : D}
    (eM : F.obj M ≅ X) (eN : F.obj N ≅ Y) (a : M ⟶ N) (b : X ⟶ Y)
    (h : F.map a ≫ eN.hom = eM.hom ≫ b) : PresentedMapNaturality.presentedMap F eM eN a = b := by
  apply (cancel_epi eM.hom).mp
  simpa only [PresentedMapNaturality.presentedMap, Category.assoc, Iso.hom_inv_id_assoc] using h

theorem composition (F : C ⥤ D) {M N P : C} {X Y Z : D}
    (eM : F.obj M ≅ X) (eN : F.obj N ≅ Y) (eP : F.obj P ≅ Z)
    (a : M ⟶ N) (b : N ⟶ P) :
    PresentedMapNaturality.presentedMap F eM eN a ≫ PresentedMapNaturality.presentedMap F eN eP b = PresentedMapNaturality.presentedMap F eM eP (a ≫ b) := by
  simp only [PresentedMapNaturality.presentedMap, F.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

theorem injective (F : C ⥤ D) [F.Faithful] {M N : C} {X Y : D}
    (eM : F.obj M ≅ X) (eN : F.obj N ≅ Y) :
    Function.Injective (PresentedMapNaturality.presentedMap F eM eN) := by
  intro a b h
  apply F.map_injective
  apply (cancel_mono eN.hom).mp
  apply (cancel_epi eM.inv).mp
  exact h

end

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Gluing OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.PresentedMorphisms

variable {R S : CommRingCat.{u}} (f : R ⟶ S) {M N : ModuleCat.{u} R}
  {X Y : (Spec R).Modules} (eM : (tilde.functor R).obj M ≅ X)
  (eN : (tilde.functor R).obj N ≅ Y) (a : M ⟶ N)

/-- The pulled-back presented morphism is the presentation of the scalar-extended module map. -/
theorem pullback_presentedMap :
    Affine.PresentedMorphisms.presentedMap (Affine.Gluing.comparison M eM f) (Affine.Gluing.comparison N eN f) ((ModuleCat.extendScalars f.hom).map a) =
      (Scheme.Modules.pullback (Spec.map f)).map (Affine.PresentedMorphisms.presentedMap eM eN a) :=
  recover_from_square (tilde.functor S) (Affine.Gluing.comparison M eM f) (Affine.Gluing.comparison N eN f)
    ((ModuleCat.extendScalars f.hom).map a)
    ((Scheme.Modules.pullback (Spec.map f)).map (Affine.PresentedMorphisms.presentedMap eM eN a))
    (Affine.PresentedMorphisms.comparison_naturality eM eN a f)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.PresentedMapComposition
