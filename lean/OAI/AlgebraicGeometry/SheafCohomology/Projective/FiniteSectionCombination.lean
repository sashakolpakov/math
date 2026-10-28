import OAI.AlgebraicGeometry.SheafCohomology.Projective.CoproductTotal
import Mathlib.Algebra.Category.ModuleCat.Basic

/-! # Finite Section Combination -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteSectionCombination

noncomputable section

/-! The value of a map from a finite coproduct is the sum of its component values. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive

universe u v w t

theorem finiteCoproduct_desc_value {C : Type u} [Category.{v} C] [Preadditive C]
    [HasFiniteBiproducts C] {R : Type w} [Ring R] (F : C ⥤ ModuleCat.{t} R) [F.Additive]
    {ι : Type} [Fintype ι] (M : ι → C) {N : C} (f : ∀ i, M i ⟶ N)
    (x : F.obj (∐ M)) :
    F.map (Sigma.desc f) x = ∑ i, F.map (f i) (F.map (CoproductMatrixComponents.finiteCoproductProjection M i) x) := by
  have h : (∑ i, CoproductMatrixComponents.finiteCoproductProjection M i ≫ f i) = Sigma.desc f := by
    conv_rhs => rw [← Category.id_comp (Sigma.desc f), ← CoproductTotal.finiteCoproduct_total M]
    rw [sum_comp]
    simp only [Category.assoc, Sigma.ι_comp_desc]
  rw [← h, F.map_sum]
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, CategoryTheory.Functor.map_comp, ModuleCat.comp_apply]

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteSectionCombination
