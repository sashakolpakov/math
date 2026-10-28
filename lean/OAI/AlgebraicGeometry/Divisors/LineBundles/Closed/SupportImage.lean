import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportDimension
import OAI.AlgebraicGeometry.CycleClass.Geometric.StratumClosure

/-! # Support Image -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportImage.BundleCycles

noncomputable section

/-!
# LineBundleCycles: actual support images under closed immersion

The image of a reduced integral support under a closed immersion is its
actual reduced image scheme. The induced morphism is an isomorphism, so
both the scheme structure and the support dimension are preserved.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Scheme} (i : X ⟶ Y) [IsClosedImmersion i]

/-- The actual reduced irreducible image of a support. -/
def closedImageSupport (W : IrreducibleCloseds X) : IrreducibleCloseds Y :=
  CycleClass.Geometric.StratumClosure.integralImageClosure (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ i)

theorem closedImageSupport_coe (W : IrreducibleCloseds X) :
    (closedImageSupport i W : Set Y) = i '' (W : Set X) := by
  change closure (Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ i)) = _
  have hr : Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ i) = i '' (W : Set X) := by
    change Set.range (i ∘ CycleClass.Geometric.GenericPoint.reducedSupportι W) = _
    rw [Set.range_comp, CycleClass.Geometric.GenericPoint.range_reducedSupportι]
  exact (congrArg closure hr).trans (i.isClosedEmbedding.isClosedMap _ W.isClosed).closure_eq

/-- The support itself is isomorphic to its reduced closed image. -/
def closedSupportImageIso (W : IrreducibleCloseds X) :
    CycleClass.Geometric.GenericPoint.reducedSupportScheme W ≅ CycleClass.Geometric.GenericPoint.reducedSupportScheme (closedImageSupport i W) := by
  let j := CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ i
  have he : IsIso (CycleClass.Geometric.StratumClosure.toReducedImageClosure j) := by
    change IsIso (j.toImage ≫ (CycleClass.Geometric.StratumClosure.reducedImageClosureIso j).hom)
    infer_instance
  exact @asIso _ _ _ _ (CycleClass.Geometric.StratumClosure.toReducedImageClosure j) he

theorem closedSupportImageIso_inclusion (W : IrreducibleCloseds X) :
    (closedSupportImageIso i W).hom ≫ CycleClass.Geometric.GenericPoint.reducedSupportι (closedImageSupport i W) =
      CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ i :=
  CycleClass.Geometric.StratumClosure.toReducedImageClosure_inclusion (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ i)

/-- The image is exactly the closure of the image of the original generic point. -/
theorem closedImageSupport_eq_pointClosure (W : IrreducibleCloseds X) :
    closedImageSupport i W = irreducibleSetEquivPoints.symm (i (irreducibleSetEquivPoints W)) := by
  apply IrreducibleCloseds.ext
  have h := (W.isIrreducible.isGenericPoint_genericPoint W.isClosed).image i.continuous
  have hc := h.def
  change closure {i (irreducibleSetEquivPoints W)} = closure (i '' (W : Set X)) at hc
  exact (closedImageSupport_coe i W).trans
    ((i.isClosedEmbedding.isClosedMap _ W.isClosed).closure_eq.symm.trans hc.symm)

theorem closedImageSupport_genericPoint (W : IrreducibleCloseds X) :
    irreducibleSetEquivPoints (closedImageSupport i W) = i (irreducibleSetEquivPoints W) :=
  (congrArg irreducibleSetEquivPoints (closedImageSupport_eq_pointClosure i W)).trans
    (irreducibleSetEquivPoints.apply_symm_apply _)

/-- Closed support images preserve the actual base-field dimension. -/
theorem closedImageSupport_dimension (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (W : IrreducibleCloseds X) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (closedImageSupport i W) f =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W (i ≫ f) := by
  have h := CycleClass.Geometric.StratumClosure.schemeTranscendenceDimension_eq_imageClosure (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ i) f
  change Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension ((CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ i) ≫ f) =
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (closedImageSupport i W) f at h
  exact h.symm.trans
    (congrArg (fun g => Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g) (Category.assoc _ _ _))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportImage.BundleCycles
