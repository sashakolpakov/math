import OAI.AlgebraicGeometry.Divisors.LineBundles.LocallyProductSupportedClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.OpenProductChart
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.PulledSupport

/-! # Supported Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.SupportedClass.Cycles

noncomputable section

/-! Canonical supported cycle classes pull back along actual affine-space
bundles, with all charts and dimensions constructed from the bundle geometry.
No global constant-rank hypothesis is needed. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

variable {E X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral E.left] [Smooth E.hom]
    [AlgebraicGeometry.IsNoetherian E.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints E)]
    [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    (f : E ⟶ X) [Smooth f.left] [GeometricallyIntegral f.left]
    (h : Affine.SpaceChartBaseChange.BundleCycles.HasAffineSpaceCharts f.left) (B : IrreducibleCloseds X.left)

local notation "C" => OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupport f.left B

include h in
omit [Smooth E.hom] [AlgebraicGeometry.IsNoetherian E.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints E)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem affineBundleSupport_codimension (p : ℕ)
    (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension B X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension C E.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension E.hom :=
  LocallyProductSupportedClass.BundleCycles.locallyProductSupport_codimension f (AffineSpace.OpenProductChart.BundleCycles.affineBundleOpenProductChart f h) B C
    (Integral.PulledSupport.BundleCycles.integralPulledSupport_coe f.left B) p hp

theorem schemeSupportedCycleClass_affineBundle (p : ℕ)
    (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension B X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
      (SchemeCycle.PreimageSupport.BundleCycles.schemeSupportPreimage_mapsTo f B C (Integral.PulledSupport.BundleCycles.integralPulledSupport_coe f.left B)) (2 * p)
      (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X B p hp) =
      Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass E C p (affineBundleSupport_codimension f h B p hp) :=
  LocallyProductSupportedClass.BundleCycles.schemeSupportedCycleClass_locally_product f (AffineSpace.OpenProductChart.BundleCycles.affineBundleOpenProductChart f h) B C
    (Integral.PulledSupport.BundleCycles.integralPulledSupport_coe f.left B) p hp (affineBundleSupport_codimension f h B p hp)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.SupportedClass.Cycles
