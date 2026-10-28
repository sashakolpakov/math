import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportedOpenPullback
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.AbsoluteProjection

/-! # Absolute Open Pullback -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.AbsoluteOpenPullback.BundleCycles

noncomputable section

/-! Open restriction of the genuine ordinary cycle class, in both degree
conventions, follows by forgetting support in the proved relative comparison. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    [IsIntegral Y.left] [Smooth Y.hom]
    [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
    (i : X ⟶ Y) [IsOpenImmersion i.left]
    (B : IrreducibleCloseds Y.left) [Nonempty (Open.SupportRestriction.BundleCycles.openSupportPullback i.left B)]
    (p : ℕ) (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension B Y.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom)

local notation "A" => OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportRestriction.BundleCycles.openRestrictedSupport i.left B
local notation "ha" => OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportOver.BundleCycles.openRestrictedSupportOver_codimension i B p hp

theorem schemeAbsoluteCycleClass_openPullback :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p) i (AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass Y B p hp) =
      AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass X A p ha := by
  have h := ConcreteCategory.congr_hom
    (CycleClass.Geometric.RelativeCohomologyExtensionNaturality.Cohomology.relativeCohomologyInclusion_naturality (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map i)
      (SupportedOpenPullback.BundleCycles.schemeOpen_support_mapsTo i B) (2 * p)) (SupportedCycleClass.BundleCycles.schemeSupportedCycleClass Y B p hp)
  exact h.symm.trans (congrArg
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X A))ᶜ (2 * p))
    (SupportedOpenPullback.BundleCycles.schemeSupportedCycleClass_openPullback i B p hp))

theorem schemeCycleClass_openPullback :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) i (AbsoluteCycleClass.BundleCycles.schemeCycleClass Y B p hp) =
      AbsoluteCycleClass.BundleCycles.schemeCycleClass X A p ha := by
  change Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) i
    (cast (congrArg (fun n => (Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) Y n : Type)) (two_mul p))
      (AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass Y B p hp)) = _
  rw [AbsoluteProjection.BundleCycles.schemeBettiMap_cast (ModuleCat.of ℚ ℚ) i (two_mul p)]
  exact congrArg (cast (congrArg (fun n => (Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) X n : Type)) (two_mul p)))
    (schemeAbsoluteCycleClass_openPullback i B p hp)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.AbsoluteOpenPullback.BundleCycles
