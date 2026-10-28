import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.SupportedClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.AbsoluteProjection

/-! # Absolute Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.AbsoluteClass.Cycles

noncomputable section

/-! The genuine ordinary cycle class commutes with affine-space bundle
pullback after forgetting support, in both standard degree conventions. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

variable {E X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral E.left] [Smooth E.hom]
    [AlgebraicGeometry.IsNoetherian E.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints E)]
    [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    (f : E ⟶ X) [Smooth f.left] [GeometricallyIntegral f.left]
    (h : Affine.SpaceChartBaseChange.BundleCycles.HasAffineSpaceCharts f.left) (B : IrreducibleCloseds X.left)
    (p : ℕ) (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension B X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)

local notation "C" => OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupport f.left B
local notation "hc" => OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.SupportedClass.Cycles.affineBundleSupport_codimension f h B p hp

theorem schemeAbsoluteCycleClass_affineBundle :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p) f (Scheme.AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass X B p hp) =
      Scheme.AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass E C p hc := by
  have ht := ConcreteCategory.congr_hom
    (CycleClass.Geometric.RelativeCohomologyExtensionNaturality.Cohomology.relativeCohomologyInclusion_naturality (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
      (SchemeCycle.PreimageSupport.BundleCycles.schemeSupportPreimage_mapsTo f B C (Integral.PulledSupport.BundleCycles.integralPulledSupport_coe f.left B)) (2 * p))
    (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X B p hp)
  exact ht.symm.trans (congrArg
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints E))
      (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion E C))ᶜ (2 * p))
    (SupportedClass.Cycles.schemeSupportedCycleClass_affineBundle f h B p hp))

theorem schemeCycleClass_affineBundle :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) f (Scheme.AbsoluteCycleClass.BundleCycles.schemeCycleClass X B p hp) =
      Scheme.AbsoluteCycleClass.BundleCycles.schemeCycleClass E C p hc := by
  change Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) f
    (cast (congrArg (fun n => (Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) X n : Type)) (two_mul p))
      (Scheme.AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass X B p hp)) = _
  rw [Scheme.AbsoluteProjection.BundleCycles.schemeBettiMap_cast (ModuleCat.of ℚ ℚ) f (two_mul p)]
  exact congrArg (cast (congrArg (fun n => (Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) E n : Type)) (two_mul p)))
    (schemeAbsoluteCycleClass_affineBundle f h B p hp)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.AbsoluteClass.Cycles
