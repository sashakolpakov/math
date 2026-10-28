import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SupportedCycleRelativeClass
import OAI.AlgebraicGeometry.ComplexMultiplication.RelativeDualAbsoluteExtension
import OAI.AlgebraicGeometry.ComplexMultiplication.RelativeAbsoluteTopPullback
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.BettiBridge

/-! # Cycle Relative Absolute -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CycleRelativeAbsolute

noncomputable section

/-! # The genuine whole-cycle relative class has the original ordinary Betti image -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace OAI.AlgebraicTopology.Singular
attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (p : ℕ) (x : CycleClassMap.OriginalCycleComponent X p)
local notation "V" => OAI.AlgebraicGeometry.ComplexMultiplication.BundledAbelianBridge.originalIntegralProjectiveVariety X
local notation "D" => OAI.AlgebraicGeometry.ComplexMultiplication.Reference.DimensionCycleSupports.originalDimensionSupport X p x
local notation "Y" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
local notation "S" => OAI.AlgebraicGeometry.Cycle.Support.cycleComponentSupport X x.val
local notation "N" => Set.range (OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.analyticInclusion (D))

local instance CMOriginalCycleRelativeAbsolute.localInstance1 : TopologicalSpace (V).analyticSpace :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.analyticTopology X

theorem originalCycleRelativeAbsolute :
    AlgebraicTopology.Singular.CohomologyTo.cohomologyMap ℚ (2 * p) (Opens.inclusionTopIso (Y)).inv
      (AlgebraicTopology.Singular.CohomologyTo.relativeCohomologyToAbsolute ℚ (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair
        (Set.univ : Set (ComplexPoint.Basic.ComplexSchemePoint X)) (S)) (2 * p)
        (SupportedCycleRelativeClass.originalSupportedCycleRelativeClass X p x)) =
    PointBettiBridge.schemeSingularCohomologyBridgeEquiv ℚ X (2 * p)
      (NormalCoclassComparison.normalCoclassCoefficient p •
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ)
          (TopCat.of (V).analyticSpace) (N)ᶜ (2 * p) (D).rationalSupportedCycleClass) := by
  let f := RelativeNeighborhoodPullback.neighborhoodToSubsetPair Set.univ (S) ≫ SupportedCycleRelativeClass.originalPointSupportPairMap X p x
  let c := NormalCoclassComparison.normalCoclassCoefficient p • (D).rationalSupportedCycleClass
  let a := RelativeSingularCochainBridge.relativeSingularCohomologyBridgeEquiv ℚ (TopCat.of (V).analyticSpace)
    (N)ᶜ (2 * p) c
  have he : (Opens.inclusionTopIso (Y)).inv ≫ f.right = (PointBettiBridge.complexPointSpaceIso X).inv := by
    ext y
    rfl
  have ht := RelativeAbsoluteTopPullback.relativeAbsoluteTopPullback ℚ (Y) (S)
    (TopPair.ofSubset (X := TopCat.of (V).analyticSpace) (N)ᶜ)
    f (PointBettiBridge.complexPointSpaceIso X).inv he (2 * p) a
  have hb := RelativeDualAbsoluteExtension.relativeSingularCohomologyBridgeEquiv_toAbsolute ℚ
    (TopCat.of (V).analyticSpace) (N)ᶜ (2 * p) c
  have hn := SingularCochainBridge.singularCohomologyBridgeEquiv_naturality ℚ
    (PointBettiBridge.complexPointSpaceIso X).inv (2 * p)
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ)
      (TopCat.of (V).analyticSpace) (N)ᶜ (2 * p) c)
  refine ht.trans ((congrArg (AlgebraicTopology.Singular.CohomologyTo.cohomologyMap ℚ (2 * p)
    (PointBettiBridge.complexPointSpaceIso X).inv) hb).trans ?_)
  simpa only [c, map_smul] using! hn.symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CycleRelativeAbsolute
