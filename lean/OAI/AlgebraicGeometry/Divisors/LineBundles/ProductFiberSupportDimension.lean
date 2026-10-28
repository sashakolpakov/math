import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.ClosedImageDimension
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.PulledSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProductDimension

/-! # Product Fiber Support Dimension -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ProductFiberSupportDimension.BundleCycles

noncomputable section

/-! The dimension of an actual product-projection support is the sum of
the integral fiber factor's dimension and the original support dimension. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

theorem productFiberSupport_dimension (C Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral C.left]
    [LocallyOfFiniteType C.hom] [Smooth C.hom] [GeometricallyIntegral C.hom]
    [AlgebraicGeometry.IsNoetherian Y.left] [LocallyOfFiniteType Y.hom]
    (W : IrreducibleCloseds Y.left) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Integral.PulledSupport.BundleCycles.integralPulledSupport (pullback.snd C.hom Y.hom) W)
        (pullback.snd C.hom Y.hom ≫ Y.hom) =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension C.hom + Foundations.Scheme.SupportDimension.supportTranscendenceDimension W Y.hom := by
  let p := pullback.snd C.hom Y.hom
  let j := Integral.PulledSupport.BundleCycles.integralPulledSupportInclusion p W
  let t := Integral.PulledSupport.BundleCycles.integralPulledSupportProjection p W
  let R := Over.mk (CycleClass.Geometric.SupportFiniteType.supportStructureMap W Y.hom)
  let : IsIntegral R.left := CycleClass.Geometric.GenericPoint.reducedSupportScheme_isIntegral W
  let : LocallyOfFiniteType R.hom := CycleClass.Geometric.SupportFiniteType.supportStructureMap_locallyOfFiniteType W Y.hom
  have hs : IsPullback (j ≫ pullback.fst C.hom Y.hom) t C.hom R.hom :=
    ((Integral.PulledSupport.BundleCycles.integralPulledSupport_isPullback p W).paste_vert (IsPullback.of_hasPullback C.hom Y.hom).flip).flip
  let e := hs.isoPullback
  have he : e.hom ≫ (pullback.fst C.hom R.hom ≫ C.hom) = j ≫ (p ≫ Y.hom) := by
    rw [← Category.assoc, hs.isoPullback_hom_fst, Category.assoc, pullback.condition]
  have H := Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion e.hom (pullback.fst C.hom R.hom ≫ C.hom)
  rw [he] at H
  exact (Integral.ClosedImageDimension.BundleCycles.integralClosedImage_dimension j (p ≫ Y.hom)).trans
    (H.trans (CycleClass.Thom.Scheme.ProductDimension.Constructions.schemeProduct_dimension C R))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ProductFiberSupportDimension.BundleCycles
