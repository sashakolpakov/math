import OAI.AlgebraicGeometry.CycleClass.Geometric.StratumClosure

/-! # Support Dimension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.SupportDimension

noncomputable section

/-! A support contained in a closed subscheme comes from a unique
irreducible closed support there, with the same function-field dimension. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Scheme} (j : Y ⟶ X) [IsClosedImmersion j]
  (C : IrreducibleCloseds X) (hC : (C : Set X) ⊆ Set.range j)

include hC in
theorem preimage_irreducible : IsIrreducible (j ⁻¹' (C : Set X)) := by
  let e := j.isClosedEmbedding.isEmbedding.toHomeomorph
  let g : C → Y := fun x => e.symm ⟨x.val, hC x.property⟩
  have hg : Continuous g := e.symm.continuous.comp
    (continuous_subtype_val.subtype_mk (fun x : C => hC x.property))
  have hgj (x : C) : j (g x) = x.val :=
    congrArg Subtype.val (e.apply_symm_apply ⟨x.val, hC x.property⟩)
  have himage : g '' (Set.univ : Set C) = j ⁻¹' (C : Set X) := by
    ext y
    constructor
    · rintro ⟨x, _, rfl⟩
      change j (g x) ∈ C
      rw [hgj]
      exact x.property
    · intro hy
      refine ⟨⟨j y, hy⟩, trivial, ?_⟩
      exact j.isClosedEmbedding.injective (hgj ⟨j y, hy⟩)
  let : IrreducibleSpace C := isIrreducible_iff_irreducibleSpace.mp C.isIrreducible
  rw [← himage]
  exact (IrreducibleSpace.isIrreducible_univ C).image g hg.continuousOn

def preimage : IrreducibleCloseds Y :=
  ⟨j ⁻¹' (C : Set X), preimage_irreducible j C hC, C.isClosed.preimage j.continuous⟩

theorem imageClosure : CycleClass.Geometric.StratumClosure.integralImageClosure (CycleClass.Geometric.GenericPoint.reducedSupportι (SupportDimension.preimage j C hC) ≫ j) = C := by
  apply IrreducibleCloseds.ext
  rw [CycleClass.Geometric.StratumClosure.integralImageClosure_coe]
  change closure (Set.range (j ∘ CycleClass.Geometric.GenericPoint.reducedSupportι (SupportDimension.preimage j C hC))) = _
  rw [Set.range_comp, CycleClass.Geometric.GenericPoint.range_reducedSupportι]
  change closure (j '' j ⁻¹' (C : Set X)) = _
  rw [Set.image_preimage_eq_inter_range, Set.inter_eq_left.mpr hC, C.isClosed.closure_eq]

theorem dimension {K : Type} [Field K] (f : X ⟶ Spec (.of K)) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (SupportDimension.preimage j C hC) (j ≫ f) = Foundations.Scheme.SupportDimension.supportTranscendenceDimension C f := by
  have hd := CycleClass.Geometric.StratumClosure.schemeTranscendenceDimension_eq_imageClosure (CycleClass.Geometric.GenericPoint.reducedSupportι (SupportDimension.preimage j C hC) ≫ j) f
  rw [imageClosure] at hd
  simpa only [Foundations.Scheme.SupportDimension.supportTranscendenceDimension, CycleClass.Geometric.SupportFiniteType.supportStructureMap, Category.assoc] using hd

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.SupportDimension
