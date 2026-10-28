import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.CodimensionPointClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ProjectionComponents

/-! # Point Component Dimension -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.PointComponentDimension.BundleCycles

noncomputable section

/-! Dimension and codimension add to the dimension of the actual
component containing a point or integral support. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

theorem projectiveSupport_dimension_add_codimension (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (W : IrreducibleCloseds X.carrier) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.structureMap + X.supportCodimension W =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (X.componentVariety (X.supportComponent W)).structureMap := by
  unfold Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.supportCodimension
  exact Nat.add_sub_of_le (CodimensionPointClass.BundleCycles.projectiveSupport_dimension_le_component X W)

theorem projectivePoint_mem_supportComponent (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (x : X.carrier) :
    x ∈ Set.range (X.componentInclusion (X.supportComponent (irreducibleSetEquivPoints.symm x))) := by
  rw [X.componentInclusion_range]
  apply X.support_subset_component (irreducibleSetEquivPoints.symm x)
  exact subset_closure rfl

theorem projectivePoint_supportComponent (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (C : irreducibleComponents X.carrier) (x : X.carrier) (hx : x ∈ Set.range (X.componentInclusion C)) :
    X.supportComponent (irreducibleSetEquivPoints.symm x) = C := by
  have hy := projectivePoint_mem_supportComponent X x
  obtain ⟨D, _, hD⟩ := Graph.ProjectionComponents.BundleCycles.projectiveComponents_cover X x
  exact (hD _ hy).trans (hD C hx).symm

theorem projectivePoint_dimension_add_codimension (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (C : irreducibleComponents X.carrier) (x : X.carrier) (hx : x ∈ Set.range (X.componentInclusion C)) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) X.structureMap +
        X.supportCodimension (irreducibleSetEquivPoints.symm x) =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (X.componentVariety C).structureMap :=
  (projectiveSupport_dimension_add_codimension X (irreducibleSetEquivPoints.symm x)).trans
    (congrArg (fun D : irreducibleComponents X.carrier => Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (X.componentVariety D).structureMap)
      (projectivePoint_supportComponent X C x hx))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.PointComponentDimension.BundleCycles
