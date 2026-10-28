import OAI.AlgebraicGeometry.CycleClass.Geometric.StratumClosure

/-! # Support Dimension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.SupportDimension

noncomputable section

/-! Restricting a support to a nonempty open chart preserves its
actual function-field dimension. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Scheme} (j : Y ⟶ X) [IsOpenImmersion j]
  (C : IrreducibleCloseds X) (h : (j ⁻¹' (C : Set X)).Nonempty)

def preimage : IrreducibleCloseds Y :=
  ⟨j ⁻¹' (C : Set X),
    C.isIrreducible.preimage j.isOpenEmbedding (by
      obtain ⟨y, hy⟩ := h
      exact ⟨j y, hy, Set.mem_range_self y⟩), C.isClosed.preimage j.continuous⟩

theorem imageClosure : CycleClass.Geometric.StratumClosure.integralImageClosure (CycleClass.Geometric.GenericPoint.reducedSupportι (SupportDimension.preimage j C h) ≫ j) = C := by
  apply IrreducibleCloseds.ext
  rw [CycleClass.Geometric.StratumClosure.integralImageClosure_coe]
  change closure (Set.range (j ∘ CycleClass.Geometric.GenericPoint.reducedSupportι (SupportDimension.preimage j C h))) = _
  rw [Set.range_comp, CycleClass.Geometric.GenericPoint.range_reducedSupportι]
  exact closure_image_preimage_of_isPreirreducible j j.isOpenEmbedding.isOpenMap C h
    C.isIrreducible.isPreirreducible C.isClosed

theorem dimension [QuasiCompact j] {K : Type} [Field K] (f : X ⟶ Spec (.of K)) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (SupportDimension.preimage j C h) (j ≫ f) =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension C f := by
  have hd := CycleClass.Geometric.StratumClosure.schemeTranscendenceDimension_eq_imageClosure (CycleClass.Geometric.GenericPoint.reducedSupportι (SupportDimension.preimage j C h) ≫ j) f
  rw [imageClosure] at hd
  simpa only [Foundations.Scheme.SupportDimension.supportTranscendenceDimension, CycleClass.Geometric.SupportFiniteType.supportStructureMap, Category.assoc] using hd

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.SupportDimension
