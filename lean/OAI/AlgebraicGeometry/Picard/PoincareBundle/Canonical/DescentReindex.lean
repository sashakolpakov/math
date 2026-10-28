import OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentReindexing
import OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackFiberComposition

/-! # Descent Reindex -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.DescentReindex

noncomputable section

/-!
# Canonical descent comparisons retain their actual values under reindexing
-/

open _root_.CategoryTheory Opposite

universe u v u' v' u'' v''

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (G : C ⥤ D) (F : Pseudofunctor (LocallyDiscrete Dᵒᵖ) Cat.{v'', u''})
  {X Y : C} (f : X ⟶ Y) (P : F.obj (.mk (op (G.obj Y))))

/-- The specified fiber-composition isomorphism is unchanged by the actual reindexing functor. -/
theorem fiberIsoTo_eq {T : C} (x : T ⟶ X) (q : T ⟶ Y) (hx : x ≫ f = q) :
    PullbackFiberComposition.fiberIsoTo (DescentReindexing.reindex G F) f P x q hx =
    PullbackFiberComposition.fiberIsoTo F (G.map f) P (G.map x) (G.map q)
      ((G.map_comp x f).symm.trans (congrArg G.map hx)) := by
  unfold PullbackFiberComposition.fiberIsoTo
  rw [DescentReindexing.mapComp_reindex G F x f q hx]
  rfl

/-- Canonical descent on a reindexed object has exactly the canonical original morphism on its image. -/
theorem ofObj_hom {T : C} (q : T ⟶ Y) (x y : T ⟶ X) (hx : x ≫ f = q) (hy : y ≫ f = q) :
    (Pseudofunctor.DescentData.ofObj (F := DescentReindexing.reindex G F)
      (f := fun (_ : PUnit.{1}) => f) P).hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy =
    (Pseudofunctor.DescentData.ofObj (F := F) (f := fun (_ : PUnit.{1}) => G.map f) P).hom
      (G.map q) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (G.map x) (G.map y)
      ((G.map_comp x f).symm.trans (congrArg G.map hx)) ((G.map_comp y f).symm.trans (congrArg G.map hy)) := by
  change (PullbackFiberComposition.fiberIsoTo (DescentReindexing.reindex G F) f P x q hx).hom ≫
    (PullbackFiberComposition.fiberIsoTo (DescentReindexing.reindex G F) f P y q hy).inv = _
  rw [fiberIsoTo_eq, fiberIsoTo_eq]
  rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.DescentReindex
