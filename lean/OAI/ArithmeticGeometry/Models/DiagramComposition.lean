import OAI.ArithmeticGeometry.Models.DiagramBaseChange

/-! # Diagram Composition -/

namespace OAI.ArithmeticGeometry.Models.DiagramComposition.Constructions.Foundations

/-! Comparing successive changes of base for a whole diagram. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v w

noncomputable def baseChangeDiagramIso
    {J : Type v} [Category.{w} J] {S T U : Scheme.{u}}
    (D : J ⥤ Over S) (f : T ⟶ S) (g : U ⟶ T) (h : U ⟶ S) (heq : g ≫ f = h) :
    (D ⋙ Over.pullback f) ⋙ Over.pullback g ≅ D ⋙ Over.pullback h := by
  let p : (D ⋙ Over.pullback h) ⋙ Over.forget U ⟶
      (D ⋙ Over.pullback f) ⋙ Over.forget T :=
    { app := fun i ↦ pullback.lift (pullback.fst (D.obj i).hom h)
        (pullback.snd (D.obj i).hom h ≫ g) (by
          erw [pullback.condition, Category.assoc, heq])
      naturality := by
        intro i j a
        apply pullback.hom_ext
        · erw [Category.assoc, pullback.lift_fst, pullback.lift_fst,
            Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst]
        · erw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd,
            Category.assoc, pullback.lift_snd, pullback.lift_snd] }
  apply DiagramBaseChange.Constructions.Foundations.genericDiagramIso g (D ⋙ Over.pullback h) (D ⋙ Over.pullback f) p
  intro i
  apply IsPullback.of_right ?_ (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback (D.obj i).hom f)
  erw [pullback.lift_fst, heq]
  exact IsPullback.of_hasPullback (D.obj i).hom h

end OAI.ArithmeticGeometry.Models.DiagramComposition.Constructions.Foundations
