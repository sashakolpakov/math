import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.PresentedMorphisms

/-! # Presented Map Fullness -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.PresentedMapFullness

noncomputable section

/-!
# Recover module morphisms from their actual affine geometric presentations
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

section

/-- A morphism with the prescribed conjugated image recovers the presented geometric morphism. -/
theorem recover {C D : Type*} [Category C] [Category D] (H : C ⥤ D)
    {M N : C} {X Y : D} (eM : H.obj M ≅ X) (eN : H.obj N ≅ Y)
    (a : M ⟶ N) (b : X ⟶ Y) (h : H.map a = eM.hom ≫ b ≫ eN.inv) :
    PresentedMapNaturality.presentedMap H eM eN a = b := by
  unfold PresentedMapNaturality.presentedMap
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

end

universe u

variable {R : CommRingCat.{u}} {M N : ModuleCat.{u} R} {X Y : (Spec R).Modules}
  (eM : (tilde.functor R).obj M ≅ X) (eN : (tilde.functor R).obj N ≅ Y) (b : X ⟶ Y)

/-- The unique module morphism underlying a map of the chosen affine presentations. -/
def moduleMap : M ⟶ N :=
  (tilde.fullyFaithfulFunctor (R := R)).preimage (eM.hom ≫ b ≫ eN.inv)

theorem map_moduleMap :
    (tilde.functor R).map (moduleMap eM eN b) = eM.hom ≫ b ≫ eN.inv :=
  (tilde.fullyFaithfulFunctor (R := R)).map_preimage _

/-- Presenting this module morphism recovers exactly the original geometric morphism. -/
theorem presentedMap_moduleMap :
    PresentedMorphisms.presentedMap eM eN (moduleMap eM eN b) = b :=
  recover (tilde.functor R) eM eN (moduleMap eM eN b) b (map_moduleMap eM eN b)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.PresentedMapFullness
