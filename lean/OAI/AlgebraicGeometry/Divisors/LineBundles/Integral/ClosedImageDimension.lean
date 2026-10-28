import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.ClosedImage
import OAI.AlgebraicGeometry.Divisors.LineBundles.ImmersionDimension

/-! # Closed Image Dimension -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.ClosedImageDimension.BundleCycles

noncomputable section

/-! An integral closed immersion identifies its scheme dimension with
the dimension of its actual reduced image support. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem integralClosedImage_dimension {A X : Scheme.{0}} [IsIntegral A]
    (i : A ⟶ X) [IsClosedImmersion i] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (CycleClass.Geometric.StratumClosure.integralImageClosure i) f = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (i ≫ f) := by
  have H := Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion (ClosedImage.BundleCycles.integralClosedImageIso i).hom
    (CycleClass.Geometric.SupportFiniteType.supportStructureMap (CycleClass.Geometric.StratumClosure.integralImageClosure i) f)
  change Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension ((ClosedImage.BundleCycles.integralClosedImageIso i).hom ≫
    (CycleClass.Geometric.GenericPoint.reducedSupportι (CycleClass.Geometric.StratumClosure.integralImageClosure i) ≫ f)) = _ at H
  rw [← Category.assoc, ClosedImage.BundleCycles.integralClosedImageIso_inclusion] at H
  exact H.symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.ClosedImageDimension.BundleCycles
