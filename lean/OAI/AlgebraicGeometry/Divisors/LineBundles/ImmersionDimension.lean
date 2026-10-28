import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportImage

/-! # Immersion Dimension -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ImmersionDimension.BundleCycles

noncomputable section

/-!
# LineBundleCycles: support dimension under locally closed immersion

The source support is open in its actual reduced image closure. The
generic-point image identifies that closure and the existing genuine
function-field comparison proves equality of dimensions.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Scheme} [AlgebraicGeometry.IsNoetherian X]
    (i : X ⟶ Y) [IsImmersion i]

omit [AlgebraicGeometry.IsNoetherian X] [IsImmersion i] in
/-- The reduced image closure of a point support is the closure of its actual image point. -/
theorem pointSupport_imageClosure (x : X) :
    CycleClass.Geometric.StratumClosure.integralImageClosure (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x) ≫ i) =
      irreducibleSetEquivPoints.symm (i x) := by
  apply IrreducibleCloseds.ext
  change closure (Set.range (i ∘ CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x))) = closure {i x}
  rw [Set.range_comp, CycleClass.Geometric.GenericPoint.range_reducedSupportι]
  change closure (i '' closure {x}) = closure {i x}
  rw [closure_image_closure i.continuous, Set.image_singleton]

/-- Locally closed immersion preserves the actual dimension of every reduced point closure. -/
theorem pointClosure_dimension_immersion (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (x : X) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (i x)) f =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (i ≫ f) := by
  have h := CycleClass.Geometric.StratumClosure.schemeTranscendenceDimension_eq_imageClosure
    (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x) ≫ i) f
  have himage := congrArg (fun Z => Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z f) (pointSupport_imageClosure i x)
  exact himage.symm.trans (h.symm.trans
    (congrArg (fun g => Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g) (Category.assoc _ _ _)))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ImmersionDimension.BundleCycles
