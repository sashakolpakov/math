import OAI.ArithmeticGeometry.Models.Scheme
import Mathlib.CategoryTheory.PathCategory.Basic

/-! # Diagram Base Change -/

namespace OAI.ArithmeticGeometry.Models.DiagramBaseChange.Constructions.Foundations

/-! Generic-fiber isomorphisms of diagrams and naturality on path categories. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v w vC uC

theorem paths_naturality_from_generators
    {V : Type v} [Quiver.{w} V] {C : Type uC} [Category.{vC} C]
    (D F : Paths V ⥤ C) (p : ∀ i, D.obj i ⟶ F.obj i)
    (h : ∀ (i j : V) (e : i ⟶ j),
      D.map ((Paths.of V).map e) ≫ p ((Paths.of V).obj j) =
        p ((Paths.of V).obj i) ≫ F.map ((Paths.of V).map e)) :
    ∀ {i j : Paths V} (f : i ⟶ j), D.map f ≫ p j = p i ≫ F.map f := by
  apply Paths.induction
  · intro i
    rw [D.map_id, F.map_id, Category.id_comp, Category.comp_id]
  · intro i j k f e hf
    rw [D.map_comp, F.map_comp, Category.assoc, h j k e,
      ← Category.assoc, hf, Category.assoc]

/-- A natural family of cartesian squares identifies the entire diagram
with the base change of its model diagram. -/
noncomputable def genericDiagramIso
    {J : Type v} [Category.{w} J] {S T : Scheme.{u}} (g : T ⟶ S)
    (D : J ⥤ Over T) (F : J ⥤ Over S)
    (p : D ⋙ Over.forget T ⟶ F ⋙ Over.forget S)
    (hp : ∀ i, IsPullback (p.app i) (D.obj i).hom (F.obj i).hom g) :
    F ⋙ Over.pullback g ≅ D :=
  (NatIso.ofComponents
    (fun i ↦ Over.isoMk (hp i).isoPullback (hp i).isoPullback_hom_snd)
    (fun {i j} f ↦ by
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · change (D.map f).left ≫ (hp j).isoPullback.hom ≫ pullback.fst (F.obj j).hom g =
          ((hp i).isoPullback.hom ≫ ((Over.pullback g).map (F.map f)).left) ≫
            pullback.fst (F.obj j).hom g
        erw [(hp j).isoPullback_hom_fst, Category.assoc, pullback.lift_fst,
          ← Category.assoc, (hp i).isoPullback_hom_fst]
        exact p.naturality f
      · change (D.map f).left ≫ (hp j).isoPullback.hom ≫ pullback.snd (F.obj j).hom g =
          ((hp i).isoPullback.hom ≫ ((Over.pullback g).map (F.map f)).left) ≫
            pullback.snd (F.obj j).hom g
        erw [(hp j).isoPullback_hom_snd, Category.assoc, pullback.lift_snd,
          (hp i).isoPullback_hom_snd]
        exact (D.map f).w)).symm

end OAI.ArithmeticGeometry.Models.DiagramBaseChange.Constructions.Foundations
