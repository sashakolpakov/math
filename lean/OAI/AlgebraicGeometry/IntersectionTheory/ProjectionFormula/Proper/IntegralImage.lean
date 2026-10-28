import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Fields

/-! # Integral Image -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.IntegralImage

noncomputable section

/-! An arbitrary proper integral scheme factors through its actual
reduced image in the smooth projective target, retaining the generic field. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {Z : Scheme} [IsIntegral Z]
  (f : Z ⟶ X.carrier) [IsProper f]

def map : Z ⟶ CycleClass.Geometric.GenericPoint.reducedSupportScheme (CycleClass.Geometric.StratumClosure.integralImageClosure f) := CycleClass.Geometric.StratumClosure.toReducedImageClosure f

theorem map_fac : map X f ≫ CycleClass.Geometric.GenericPoint.reducedSupportι (CycleClass.Geometric.StratumClosure.integralImageClosure f) = f :=
  CycleClass.Geometric.StratumClosure.toReducedImageClosure_inclusion f

instance map_isProper : IsProper (map X f) := by
  let : IsProper (map X f ≫ CycleClass.Geometric.GenericPoint.reducedSupportι (CycleClass.Geometric.StratumClosure.integralImageClosure f)) := by
    rw [map_fac]
    infer_instance
  exact IsProper.of_comp (map X f) (CycleClass.Geometric.GenericPoint.reducedSupportι (CycleClass.Geometric.StratumClosure.integralImageClosure f))

theorem map_surjective : Function.Surjective (map X f) := by
  intro y
  have hy : CycleClass.Geometric.GenericPoint.reducedSupportι (CycleClass.Geometric.StratumClosure.integralImageClosure f) y ∈ (CycleClass.Geometric.StratumClosure.integralImageClosure f : Set X.carrier) := by
    rw [← CycleClass.Geometric.GenericPoint.range_reducedSupportι]
    exact ⟨y, rfl⟩
  rw [CycleClass.Geometric.StratumClosure.integralImageClosure_coe, f.isClosedMap.isClosed_range.closure_eq] at hy
  obtain ⟨z, hz⟩ := hy
  refine ⟨z, (CycleClass.Geometric.GenericPoint.reducedSupportι (CycleClass.Geometric.StratumClosure.integralImageClosure f)).isEmbedding.injective ?_⟩
  have he := congrArg (fun k : Z ⟶ X.carrier => k z) (map_fac X f)
  exact he.trans hz

theorem map_genericPoint : map X f (genericPoint Z) =
    genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme (CycleClass.Geometric.StratumClosure.integralImageClosure f)) := by
  apply IsGenericPoint.eq _ (genericPoint_spec _)
  have h := (genericPoint_spec Z).image (map X f).continuous
  simpa only [Set.image_univ, (map_surjective X f).range_eq, closure_univ] using h

theorem map_over : map X f ≫ CycleClass.Geometric.SupportFiniteType.supportStructureMap (CycleClass.Geometric.StratumClosure.integralImageClosure f) X.structureMap = f ≫ X.structureMap := by
  rw [CycleClass.Geometric.SupportFiniteType.supportStructureMap, ← Category.assoc, map_fac]

theorem dimension_le : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (CycleClass.Geometric.StratumClosure.integralImageClosure f) X.structureMap ≤
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (f ≫ X.structureMap) := by
  have h := Cycles.Functoriality.FunctionFields.Construction.dimension_le_of_genericPoint (map X f) (map_genericPoint X f)
    (CycleClass.Geometric.SupportFiniteType.supportStructureMap (CycleClass.Geometric.StratumClosure.integralImageClosure f) X.structureMap)
  rw [map_over] at h
  exact h

theorem field_finite
    (hd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (CycleClass.Geometric.StratumClosure.integralImageClosure f) X.structureMap =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (f ≫ X.structureMap)) :
    letI := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (map X f) (map_genericPoint X f)).hom.toAlgebra
    Module.Finite (CycleClass.Geometric.GenericPoint.reducedSupportScheme (CycleClass.Geometric.StratumClosure.integralImageClosure f)).functionField Z.functionField := by
  apply Cycles.Functoriality.FunctionFields.Construction.genericField_extension_finite (map X f) (map_genericPoint X f)
    (CycleClass.Geometric.SupportFiniteType.supportStructureMap (CycleClass.Geometric.StratumClosure.integralImageClosure f) X.structureMap)
  rw [map_over]
  exact hd

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.IntegralImage
