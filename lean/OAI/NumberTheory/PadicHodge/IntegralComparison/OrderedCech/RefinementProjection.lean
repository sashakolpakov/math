import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Refinement

/-! # Refinement Projection -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.RefinementProjection

noncomputable section

/-! The original ordinary-to-ordered projection commutes with actual
cover refinement on cohomology, through the signed-sorting homotopy. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {D : Type v} [Category D] [Abelian D] [HasProducts.{u} D] [HasCoproducts.{0} D]
  {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]
  (U : ι → C) (V : κ → C)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)
  (P : Cᵒᵖ ⥤ D) (q : ℕ)

omit [HasCoproducts D] in
theorem homology :
    homologyMap (Projection.map U P) q ≫
      homologyMap (Refinement.map U V r P) q =
    homologyMap (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r P) q ≫
      homologyMap (Projection.map V P) q := by
  have hi : homologyMap (Projection.map U P) q ≫
      homologyMap (Retraction.inclusion U P) q = 𝟙 _ := by
    rw [← homologyMap_comp, (Homotopy.homotopy U P).homologyMap_eq q,
      homologyMap_id]
  rw [Refinement.map_eq, homologyMap_comp, homologyMap_comp,
    ← Category.assoc, hi, Category.id_comp]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.RefinementProjection
