import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Composition Morphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.CompositionMorphism

noncomputable section

/-! Transport of a family morphism between iterated and composite pullback, with its exact composition and invertibility laws. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S T U : Scheme.{u}} (f : U ⟶ T) (g : T ⟶ S) {X Y Z : Over S}

def overPullbackCompositionMorphism (h : (Over.pullback g).obj X ⟶ (Over.pullback g).obj Y) :
    (Over.pullback (f ≫ g)).obj X ⟶ (Over.pullback (f ≫ g)).obj Y :=
  (Over.pullbackComp f g).hom.app X ≫ (Over.pullback f).map h ≫ (Over.pullbackComp f g).inv.app Y

theorem overPullbackCompositionMorphism_comp (h : (Over.pullback g).obj X ⟶ (Over.pullback g).obj Y)
    (p : Y ⟶ Z) :
    overPullbackCompositionMorphism f g h ≫ (Over.pullback (f ≫ g)).map p =
      overPullbackCompositionMorphism f g (h ≫ (Over.pullback g).map p) := by
  simp only [overPullbackCompositionMorphism, Functor.map_comp, Category.assoc]
  rw [← (Over.pullbackComp f g).inv.naturality p]
  rfl

theorem overPullbackCompositionMorphism_map (h : X ⟶ Y) :
    overPullbackCompositionMorphism f g ((Over.pullback g).map h) = (Over.pullback (f ≫ g)).map h := by
  unfold overPullbackCompositionMorphism
  have hn := (Over.pullbackComp f g).hom.naturality h
  change (Over.pullback (f ≫ g)).map h ≫ (Over.pullbackComp f g).hom.app Y =
    (Over.pullbackComp f g).hom.app X ≫ (Over.pullback f).map ((Over.pullback g).map h) at hn
  rw [← Category.assoc, ← hn]
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

theorem overPullbackCompositionMorphism_factorization
    (h : (Over.pullback g).obj X ⟶ (Over.pullback g).obj Y) (j : Y ⟶ Z) (i : X ⟶ Z)
    (hh : h ≫ (Over.pullback g).map j = (Over.pullback g).map i) :
    overPullbackCompositionMorphism f g h ≫ (Over.pullback (f ≫ g)).map j =
      (Over.pullback (f ≫ g)).map i := by
  rw [overPullbackCompositionMorphism_comp, hh, overPullbackCompositionMorphism_map]

theorem overPullbackCompositionMorphism_isIso_iff
    (h : (Over.pullback g).obj X ⟶ (Over.pullback g).obj Y) :
    IsIso (overPullbackCompositionMorphism f g h) ↔ IsIso ((Over.pullback f).map h) := by
  simp only [overPullbackCompositionMorphism, isIso_comp_left_iff, isIso_comp_right_iff]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.CompositionMorphism
