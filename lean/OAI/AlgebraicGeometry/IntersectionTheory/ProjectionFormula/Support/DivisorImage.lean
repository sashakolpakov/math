import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedSupport
import OAI.AlgebraicGeometry.DivisorClass.Chern.SupportCodimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Grading

/-! # Divisor Image -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.DivisorImage

noncomputable section

/-! Divisors inside an arbitrary integral cycle support have exactly one
higher ambient codimension. Their images retain the actual generic points
and support function-field dimensions. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (W : IrreducibleCloseds X.carrier)

def image (Z : IrreducibleCloseds (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) : IrreducibleCloseds X.carrier :=
  CycleClass.Geometric.StratumClosure.integralImageClosure (CycleClass.Geometric.GenericPoint.reducedSupportι Z ≫ CycleClass.Geometric.GenericPoint.reducedSupportι W)

theorem image_point (Z : IrreducibleCloseds (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) :
    CycleClass.Thom.IntersectionGeometry.supportPoint (image X W Z) = CycleClass.Geometric.GenericPoint.reducedSupportι W (CycleClass.Thom.IntersectionGeometry.supportPoint Z) := by
  have h := Closed.ImmersionSupport.support_point (CycleClass.Geometric.GenericPoint.reducedSupportι Z ≫ CycleClass.Geometric.GenericPoint.reducedSupportι W)
  change CycleClass.Thom.IntersectionGeometry.supportPoint (image X W Z) = CycleClass.Geometric.GenericPoint.reducedSupportι W (CycleClass.Geometric.GenericPoint.reducedSupportι Z
    (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z))) at h
  rwa [CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq] at h

theorem image_injective : Function.Injective (image X W) := by
  intro A B h
  apply irreducibleSetEquivPoints.injective
  apply (CycleClass.Geometric.GenericPoint.reducedSupportι W).isEmbedding.injective
  exact (image_point X W A).symm.trans ((congrArg CycleClass.Thom.IntersectionGeometry.supportPoint h).trans (image_point X W B))

theorem image_le (Z : IrreducibleCloseds (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) : image X W Z ≤ W := by
  apply (Supports.supportPoint_mem_iff_subset
    (⟨(W : Set X.carrier), W.isClosed⟩ : Closeds X.carrier) (image X W Z)).mp
  change CycleClass.Thom.IntersectionGeometry.supportPoint (image X W Z) ∈ (W : Set X.carrier)
  rw [image_point, ← CycleClass.Geometric.GenericPoint.range_reducedSupportι]
  exact ⟨CycleClass.Thom.IntersectionGeometry.supportPoint Z, rfl⟩

theorem dimension (Z : IrreducibleCloseds (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (image X W Z) X.structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z (CycleClass.Geometric.SupportFiniteType.supportStructureMap W X.structureMap) := by
  have h := CycleClass.Geometric.StratumClosure.schemeTranscendenceDimension_eq_imageClosure
    (CycleClass.Geometric.GenericPoint.reducedSupportι Z ≫ CycleClass.Geometric.GenericPoint.reducedSupportι W) X.structureMap
  simpa only [image, Foundations.Scheme.SupportDimension.supportTranscendenceDimension, CycleClass.Geometric.SupportFiniteType.supportStructureMap, Category.assoc] using h.symm

theorem codimension (m : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (Z : IrreducibleCloseds (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) (hZ : Order.coheight (CycleClass.Thom.IntersectionGeometry.supportPoint Z) = 1) :
    X.supportCodimension (image X W Z) = X.supportCodimension W + 1 := by
  have hd := DivisorClass.Chern.SupportCodimension.Construction.pointClosure_dimension_add_one
    (CycleClass.Geometric.SupportFiniteType.supportStructureMap W X.structureMap) (CycleClass.Thom.IntersectionGeometry.supportPoint Z) hZ
  have he : irreducibleSetEquivPoints.symm (CycleClass.Thom.IntersectionGeometry.supportPoint Z) = Z :=
    irreducibleSetEquivPoints.symm_apply_apply Z
  rw [he] at hd
  change Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z (CycleClass.Geometric.SupportFiniteType.supportStructureMap W X.structureMap) + 1 =
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.structureMap at hd
  have hW := Grading.supportDimension_add_codimension X m W
  have hA := Grading.supportDimension_add_codimension X m (image X W Z)
  rw [dimension] at hA
  omega

theorem image_innerSupport (A : IrreducibleCloseds X.carrier) (hAW : A ≤ W) :
    image X W (NestedSupport.innerSupport X.carrier A W hAW) = A := by
  apply irreducibleSetEquivPoints.injective
  change CycleClass.Thom.IntersectionGeometry.supportPoint (image X W (NestedSupport.innerSupport X.carrier A W hAW)) = CycleClass.Thom.IntersectionGeometry.supportPoint A
  rw [image_point, NestedSupport.innerSupport_point, CycleClass.Thom.IntersectionGeometry.supportPreimage_spec]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.DivisorImage
