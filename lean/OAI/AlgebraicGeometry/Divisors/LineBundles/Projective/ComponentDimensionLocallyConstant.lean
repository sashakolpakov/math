import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.PointComponentDimension
import Mathlib.Topology.LocallyConstant.Basic

/-! # Component Dimension Locally Constant -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.ComponentDimensionLocallyConstant.BundleCycles

noncomputable section

/-! The dimension of the actual projective component containing a point
is locally constant, including for presentations of mixed dimension. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

theorem projectivePointSupportComponent_locallyConstant (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) :
    IsLocallyConstant (fun x : X.carrier => X.supportComponent (irreducibleSetEquivPoints.symm x)) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  let C := X.supportComponent (irreducibleSetEquivPoints.symm x)
  let : IsOpenImmersion (X.componentInclusion C) := X.componentInclusion_isOpenImmersion C
  refine ⟨(X.componentInclusion C).opensRange, (X.componentInclusion C).opensRange.isOpen,
    PointComponentDimension.BundleCycles.projectivePoint_mem_supportComponent X x, ?_⟩
  intro y hy
  exact PointComponentDimension.BundleCycles.projectivePoint_supportComponent X C y hy

theorem projectivePointComponentDimension_locallyConstant (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) :
    IsLocallyConstant (fun x : X.carrier => Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension
      (X.componentVariety (X.supportComponent (irreducibleSetEquivPoints.symm x))).structureMap) :=
  (projectivePointSupportComponent_locallyConstant X).comp
    (fun C : irreducibleComponents X.carrier => Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (X.componentVariety C).structureMap)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.ComponentDimensionLocallyConstant.BundleCycles
