import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Natural Group Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.NaturalGroupComparison

noncomputable section

/-! A natural comparison between finite-product-preserving functors
preserves their induced actual group structures. -/

open _root_.CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem natural_group_comparison
    {C D : Type*} [Category* C] [CartesianMonoidalCategory C]
    [Category* D] [CartesianMonoidalCategory D]
    (F G : C ⥤ D) [F.Monoidal] [G.Monoidal] (e : F ≅ G)
    (A : C) [GrpObj A] : IsMonHom (e.app A).hom := by
  have hn {X Y : C} (f : X ⟶ Y) : F.map f ≫ (e.app Y).hom = (e.app X).hom ≫ G.map f := e.hom.naturality f
  refine { one_hom := ?_, mul_hom := ?_ }
  · change (Functor.LaxMonoidal.ε F ≫ F.map (MonObj.one : 𝟙_ C ⟶ A)) ≫ (e.app A).hom =
      Functor.LaxMonoidal.ε G ≫ G.map (MonObj.one : 𝟙_ C ⟶ A)
    rw [Category.assoc, hn, ← Category.assoc]
    exact congrArg (fun k => k ≫ G.map (MonObj.one : 𝟙_ C ⟶ A)) (NatTrans.IsMonoidal.unit (τ := e.hom))
  · change (Functor.LaxMonoidal.μ F A A ≫ F.map (MonObj.mul : A ⊗ A ⟶ A)) ≫ (e.app A).hom =
      ((e.app A).hom ⊗ₘ (e.app A).hom) ≫
        (Functor.LaxMonoidal.μ G A A ≫ G.map (MonObj.mul : A ⊗ A ⟶ A))
    rw [Category.assoc, hn, ← Category.assoc, ← Category.assoc]
    exact congrArg (fun k => k ≫ G.map (MonObj.mul : A ⊗ A ⟶ A)) (NatTrans.IsMonoidal.tensor (τ := e.hom) A A)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.NaturalGroupComparison
