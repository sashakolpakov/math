import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-! # Product Pullback Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.ProductPullbackNaturality.FrameProductPullbackNaturality

noncomputable section

/-! Product diagrams for geometric frame pullback are natural under
compatible frame maps; preservation of products is unnecessary. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] [HasBinaryProducts C]
  {D : Type uD} [Category.{vD} D] [HasBinaryProducts D]
  (G : C ⥤ D) {F F' U : C} {H H' : D}
  (a : F ⟶ F') (b : H ⟶ H') (α : G.obj F ⟶ H) (α' : G.obj F' ⟶ H')
  (h : G.map a ≫ α' = α ≫ b)

include h in
theorem square :
    G.map (prod.map a (𝟙 U)) ≫ prod.lift (G.map prod.fst ≫ α') (G.map prod.snd) =
      prod.lift (G.map prod.fst ≫ α) (G.map prod.snd) ≫ prod.map b (𝟙 (G.obj U)) := by
  apply prod.hom_ext
  · simp only [Category.assoc, prod.lift_fst, prod.map_fst, prod.lift_fst_assoc]
    rw [← Category.assoc, ← G.map_comp, prod.map_fst, G.map_comp, Category.assoc, h]
  · simp only [Category.assoc, prod.lift_snd, prod.map_snd, Category.comp_id]
    rw [← G.map_comp, prod.map_snd, Category.comp_id]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.ProductPullbackNaturality.FrameProductPullbackNaturality
