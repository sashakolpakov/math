import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Natural Coproduct -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.NaturalCoproduct.Category

noncomputable section

/-! A natural comparison that is invertible on each summand is invertible on a preserved coproduct. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v u' v'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {ι : Type} [HasCoproductsOfShape ι C] [HasCoproductsOfShape ι D]
  {F G : C ⥤ D} (τ : F ⟶ G) (M : ι → C)

theorem naturalComparison_coproduct_square :
    CategoryTheory.Limits.Sigma.map (fun i => τ.app (M i)) ≫ sigmaComparison G M =
      sigmaComparison F M ≫ τ.app (∐ M) := by
  apply CategoryTheory.Limits.Sigma.hom_ext
  intro i
  rw [← Category.assoc, CategoryTheory.Limits.Sigma.ι_map, Category.assoc, ι_comp_sigmaComparison,
    ← Category.assoc, ι_comp_sigmaComparison]
  exact (τ.naturality (CategoryTheory.Limits.Sigma.ι M i)).symm

theorem naturalComparison_coproduct_isIso
    [PreservesColimit (Discrete.functor M) F] [PreservesColimit (Discrete.functor M) G]
    [∀ i, IsIso (τ.app (M i))] : IsIso (τ.app (∐ M)) := by
  let E := asIso (sigmaComparison F M)
  have h : τ.app (∐ M) = E.inv ≫ CategoryTheory.Limits.Sigma.map (fun i => τ.app (M i)) ≫ sigmaComparison G M :=
    (E.inv_hom_id_assoc (τ.app (∐ M))).symm.trans
      (congrArg (E.inv ≫ ·) (naturalComparison_coproduct_square τ M).symm)
  rw [h]
  infer_instance

omit [HasCoproductsOfShape ι C] [HasCoproductsOfShape ι D] in
theorem naturalComparison_isIso_of_iso {A B : C} (e : A ≅ B) [IsIso (τ.app A)] : IsIso (τ.app B) := by
  let E := F.mapIso e
  have h : τ.app B = E.inv ≫ τ.app A ≫ G.map e.hom :=
    (E.inv_hom_id_assoc (τ.app B)).symm.trans (congrArg (E.inv ≫ ·) (τ.naturality e.hom))
  rw [h]
  infer_instance

end

end OAI.AlgebraicGeometry.Comparison.Betti.NaturalCoproduct.Category
