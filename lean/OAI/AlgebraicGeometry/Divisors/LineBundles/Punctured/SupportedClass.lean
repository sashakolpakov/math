import OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.ProductCharts
import OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.SupportPreimage
import OAI.AlgebraicGeometry.Divisors.LineBundles.LocallyProductSupportedClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.AbsoluteProjection

/-! # Supported Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.SupportedClass.BundleCycles

noncomputable section

/-! Canonical supported and ordinary cycle classes commute with the actual punctured-deformation projection for every integral closed support. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (I : X.left.IdealSheafData)
  [IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  [IsIntegral (ProductCharts.BundleCycles.puncturedDeformationOver X I).left] [Smooth (ProductCharts.BundleCycles.puncturedDeformationOver X I).hom]
  [AlgebraicGeometry.IsNoetherian (ProductCharts.BundleCycles.puncturedDeformationOver X I).left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (ProductCharts.BundleCycles.puncturedDeformationOver X I))]
  (B : IrreducibleCloseds X.left) (p : ℕ)
  (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension B X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
  (hc : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (SupportExtension.BundleCycles.puncturedExtendedSupport I B) (ProductCharts.BundleCycles.puncturedDeformationOver X I).hom + p =
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (ProductCharts.BundleCycles.puncturedDeformationOver X I).hom)

theorem schemeSupportedCycleClass_puncturedProjection :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (ProductCharts.BundleCycles.puncturedProjectionOver X I))
      (SchemeCycle.PreimageSupport.BundleCycles.schemeSupportPreimage_mapsTo (ProductCharts.BundleCycles.puncturedProjectionOver X I) B (SupportExtension.BundleCycles.puncturedExtendedSupport I B)
        (SupportPreimage.BundleCycles.puncturedExtendedSupport_coe I B)) (2 * p) (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X B p hp) =
      Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass (ProductCharts.BundleCycles.puncturedDeformationOver X I) (SupportExtension.BundleCycles.puncturedExtendedSupport I B) p hc :=
  LocallyProductSupportedClass.BundleCycles.schemeSupportedCycleClass_locally_product (ProductCharts.BundleCycles.puncturedProjectionOver X I) (ProductCharts.BundleCycles.puncturedOpenProductChart X I)
    B (SupportExtension.BundleCycles.puncturedExtendedSupport I B) (SupportPreimage.BundleCycles.puncturedExtendedSupport_coe I B) p hp hc

theorem schemeAbsoluteCycleClass_puncturedProjection :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p) (ProductCharts.BundleCycles.puncturedProjectionOver X I)
      (Scheme.AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass X B p hp) =
      Scheme.AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass (ProductCharts.BundleCycles.puncturedDeformationOver X I) (SupportExtension.BundleCycles.puncturedExtendedSupport I B) p hc := by
  have h := ConcreteCategory.congr_hom
    (CycleClass.Geometric.RelativeCohomologyExtensionNaturality.Cohomology.relativeCohomologyInclusion_naturality (ModuleCat.of ℚ ℚ)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (ProductCharts.BundleCycles.puncturedProjectionOver X I))
      (SchemeCycle.PreimageSupport.BundleCycles.schemeSupportPreimage_mapsTo (ProductCharts.BundleCycles.puncturedProjectionOver X I) B (SupportExtension.BundleCycles.puncturedExtendedSupport I B)
        (SupportPreimage.BundleCycles.puncturedExtendedSupport_coe I B)) (2 * p)) (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X B p hp)
  exact h.symm.trans (congrArg
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (ProductCharts.BundleCycles.puncturedDeformationOver X I)))
      (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion (ProductCharts.BundleCycles.puncturedDeformationOver X I) (SupportExtension.BundleCycles.puncturedExtendedSupport I B)))ᶜ (2 * p))
    (schemeSupportedCycleClass_puncturedProjection X I B p hp hc))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.SupportedClass.BundleCycles
