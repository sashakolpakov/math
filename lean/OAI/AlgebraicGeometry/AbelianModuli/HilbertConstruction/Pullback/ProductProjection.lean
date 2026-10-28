import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.FamilyBaseChange

/-! # Product Projection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.ProductProjection

noncomputable section

/-! The canonical product comparison under base change identifies both actual projection morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

variable {S T : Scheme.{u}} (c : T ⟶ S) (A B : Over S)

theorem overPullbackProductIso_inv_fst :
    (Functor.Monoidal.μIso (Over.pullback c) A B).inv ≫
      fst ((Over.pullback c).obj A) ((Over.pullback c).obj B) = (Over.pullback c).map (fst A B) := by
  apply (cancel_epi (Functor.Monoidal.μIso (Over.pullback c) A B).hom).mp
  rw [Iso.hom_inv_id_assoc]
  exact (Functor.Monoidal.μ_fst (Over.pullback c) A B).symm

theorem overPullbackProductIso_inv_snd :
    (Functor.Monoidal.μIso (Over.pullback c) A B).inv ≫
      snd ((Over.pullback c).obj A) ((Over.pullback c).obj B) = (Over.pullback c).map (snd A B) := by
  apply (cancel_epi (Functor.Monoidal.μIso (Over.pullback c) A B).hom).mp
  rw [Iso.hom_inv_id_assoc]
  exact (Functor.Monoidal.μ_snd (Over.pullback c) A B).symm

def overPullbackProductMap {X : Over T} (h : X ⟶ (Over.pullback c).obj (A ⊗ B)) :
    X ⟶ (Over.pullback c).obj A ⊗ (Over.pullback c).obj B :=
  h ≫ (Functor.Monoidal.μIso (Over.pullback c) A B).inv

theorem overPullbackProductMap_fst {X : Over T} (h : X ⟶ (Over.pullback c).obj (A ⊗ B)) :
    overPullbackProductMap c A B h ≫ fst ((Over.pullback c).obj A) ((Over.pullback c).obj B) =
      h ≫ (Over.pullback c).map (fst A B) := by
  rw [overPullbackProductMap, Category.assoc, overPullbackProductIso_inv_fst]

theorem overPullbackProductMap_snd {X : Over T} (h : X ⟶ (Over.pullback c).obj (A ⊗ B)) :
    overPullbackProductMap c A B h ≫ snd ((Over.pullback c).obj A) ((Over.pullback c).obj B) =
      h ≫ (Over.pullback c).map (snd A B) := by
  rw [overPullbackProductMap, Category.assoc, overPullbackProductIso_inv_snd]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.ProductProjection
