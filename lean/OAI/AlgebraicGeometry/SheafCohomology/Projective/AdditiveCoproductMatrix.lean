import OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CoproductTotal

/-! # Additive Coproduct Matrix -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductMatrix

noncomputable section

/-! Component matrices compute an additive functor's action on finite coproducts. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive
universe u v w t
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable {R : Type w} [Ring R] (F : C ⥤ ModuleCat.{t} R) [F.Additive]
variable {ι κ : Type} [Fintype ι] [Fintype κ]

theorem additiveCoproductIsoPi_hom_apply (M : ι → C) (x : F.obj (∐ M)) (i : ι) :
    (AdditiveCoproductSections.additiveCoproductIsoPi F M).hom x i = F.map (CoproductMatrixComponents.finiteCoproductProjection M i) x :=
  ConcreteCategory.congr_hom (AdditiveCoproductSections.additiveCoproductIsoPi_hom_projection F M i) x

theorem additiveCoproduct_sum_components (M : ι → C) (x : F.obj (∐ M)) :
    ∑ i, F.map (Sigma.ι M i) ((AdditiveCoproductSections.additiveCoproductIsoPi F M).hom x i) = x := by
  have hcoords : ∑ i, F.map (Sigma.ι M i) ((AdditiveCoproductSections.additiveCoproductIsoPi F M).hom x i) =
      ∑ i, F.map (Sigma.ι M i) (F.map (CoproductMatrixComponents.finiteCoproductProjection M i) x) := by
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun y => F.map (Sigma.ι M i) y)
      (additiveCoproductIsoPi_hom_apply F M x i)
  rw [hcoords]
  have h := congrArg F.map (CoproductTotal.finiteCoproduct_total M)
  rw [F.map_sum, F.map_id] at h
  have hx := ConcreteCategory.congr_hom h x
  change (∑ i, F.map (CoproductMatrixComponents.finiteCoproductProjection M i ≫ Sigma.ι M i)).hom x = x at hx
  rw [ModuleCat.hom_sum, LinearMap.sum_apply] at hx
  simpa only [F.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] using hx

theorem additiveCoproductMatrix_apply (M : ι → C) (N : κ → C)
    (f : (∐ M) ⟶ ∐ N) (x : F.obj (∐ M)) (j : κ) :
    (AdditiveCoproductSections.additiveCoproductIsoPi F N).hom (F.map f x) j =
      ∑ i, F.map (Sigma.ι M i ≫ f ≫ CoproductMatrixComponents.finiteCoproductProjection N j)
        ((AdditiveCoproductSections.additiveCoproductIsoPi F M).hom x i) := by
  rw [additiveCoproductIsoPi_hom_apply]
  conv_lhs => rw [← additiveCoproduct_sum_components F M x]
  simp only [map_sum, F.map_comp, ConcreteCategory.comp_apply]

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductMatrix
