import OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-! # Descent Reindexing -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentReindexing

noncomputable section

/-!
# Pullback of descent morphisms commutes with reindexing the base category
-/

open _root_.CategoryTheory Opposite

universe u₁ u₂ v₁ v₂ w₁ w₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  (G : C ⥤ D) (F : Pseudofunctor (LocallyDiscrete Dᵒᵖ) Cat.{w₁,w₂})

/-- Reindex a category of geometric objects along a functor on base objects. -/
def reindex : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w₁,w₂} :=
  G.op.toPseudofunctor.comp F

theorem mapComp_reindex {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (h : f ≫ g = fg) :
    (reindex G F).mapComp' g.op.toLoc f.op.toLoc fg.op.toLoc (by rw [← h]; rfl) =
      F.mapComp' (G.map g).op.toLoc (G.map f).op.toLoc (G.map fg).op.toLoc
        (by rw [← h, G.map_comp]; rfl) := by
  subst fg
  change (G.op.toPseudofunctor.comp F).mapComp' g.op.toLoc f.op.toLoc
    (g.op.toLoc ≫ f.op.toLoc) rfl = _
  rw [Pseudofunctor.mapComp'_eq_mapComp, Pseudofunctor.comp_mapComp,
    Functor.toPseudofunctor_mapComp]
  unfold Pseudofunctor.mapComp'
  rfl

/-- Pulling a descent morphism after reindexing is the original pullback on the mapped base objects. -/
theorem pullHom_reindex {X₁ X₂ Y Y' : C}
    {L₁ : F.obj (.mk (op (G.obj X₁)))} {L₂ : F.obj (.mk (op (G.obj X₂)))}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (a : ((reindex G F).map f₁.op.toLoc).toFunctor.obj L₁ ⟶
      ((reindex G F).map f₂.op.toLoc).toFunctor.obj L₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := reindex G F) a g gf₁ gf₂ h₁ h₂ =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F) a (G.map g) (G.map gf₁) (G.map gf₂)
        ((G.map_comp g f₁).symm.trans (congrArg G.map h₁))
        ((G.map_comp g f₂).symm.trans (congrArg G.map h₂)) := by
  unfold Pseudofunctor.LocallyDiscreteOpToCat.pullHom
  rw [mapComp_reindex G F g f₁ gf₁ h₁, mapComp_reindex G F g f₂ gf₂ h₂]
  rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentReindexing
