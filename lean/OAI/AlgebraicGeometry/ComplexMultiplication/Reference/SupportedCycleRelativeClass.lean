import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RegularThomSection
import OAI.AlgebraicGeometry.ComplexMultiplication.SectionOnOpenUnit
import OAI.AlgebraicGeometry.CycleClass.Geometric.Span

/-! # Supported Cycle Relative Class -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SupportedCycleRelativeClass

noncomputable section

/-! # The actual whole-cycle class restricts to the actual original regular Thom class -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace OAI.AlgebraicTopology.Singular

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (p : ℕ) (x : CycleClassMap.OriginalCycleComponent X p)

local notation "V" => OAI.AlgebraicGeometry.ComplexMultiplication.BundledAbelianBridge.originalIntegralProjectiveVariety X
local notation "D" => OAI.AlgebraicGeometry.ComplexMultiplication.Reference.DimensionCycleSupports.originalDimensionSupport X p x
local notation "OX" => OAI.AlgebraicGeometry.Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpenOver X x.val
local notation "i" => OAI.AlgebraicGeometry.Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLiftOver X x.val
local notation "B" => Set.range (OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map (i))
local notation "SX" => OAI.AlgebraicGeometry.Cycle.Support.cycleComponentSupport X x.val
local notation "NX" => Set.range (OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.analyticInclusion
  (DimensionCycleSupports.originalDimensionSupport X p x))
local notation "H" => OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RegularAmbientHomeomorph.originalRegularAmbientHomeomorph X p x

local instance CMOriginalSupportedCycleRelativeClass.localInstance1 : TopologicalSpace (V).analyticSpace :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.analyticTopology X
local instance CMOriginalSupportedCycleRelativeClass.localInstance2 : TopologicalSpace (D).regularAnalyticSpace :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.analyticTopology (D).regularOver

def originalPointSupportPairMap :
    TopPair.ofSubset (X := TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) (SX)ᶜ ⟶
      TopPair.ofSubset (X := TopCat.of (V).analyticSpace) (NX)ᶜ :=
  RelativeDualAbsoluteExtension.originalSubsetPairMap (PointBettiBridge.complexPointSpaceIso X).inv (by
    intro y hy
    change (PointBettiBridge.complexPointSpaceIso X).inv y ∉ (NX)
    intro hs
    have he := CycleSupport.originalDimensionSupport_analyticSupport X p x
    exact hy ((congrArg (fun T => (PointBettiBridge.complexPointSpaceIso X).inv y ∈ T) he).mp hs))

/-- The genuine native whole-cycle class on the unchanged original point space and support. -/
def originalSupportedCycleRelativeClass :
    AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ
      (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (Set.univ : Set (ComplexPoint.Basic.ComplexSchemePoint X)) (SX)) (2 * p) :=
  AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ (2 * p)
    (RelativeNeighborhoodPullback.neighborhoodToSubsetPair Set.univ (SX) ≫ originalPointSupportPairMap X p x)
    (RelativeSingularCochainBridge.relativeSingularCohomologyBridgeEquiv ℚ (TopCat.of (V).analyticSpace)
      (NX)ᶜ (2 * p) (NormalCoclassComparison.normalCoclassCoefficient p • (D).rationalSupportedCycleClass))

theorem originalSupportedCycleRelativeClass_regularPullback :
    AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ (2 * p)
      (RelativeNeighborhoodPullback.neighborhoodSupportPairMap
        (ComplexPoint.Basic.Point.continuousMap (ComplexPoint.Basic.ComplexSchemePoint.openInclusion X (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x.val)))
        (B) (SX) (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLiftAmbientMap_support X x.val)
        Set.univ Set.univ (fun _ _ => Set.mem_univ _))
      (originalSupportedCycleRelativeClass X p x) =
    RegularThomRelative.originalRegularThomRelativeClass X p x := by
  let g := ComplexPoint.Basic.Point.continuousMap
    (ComplexPoint.Basic.ComplexSchemePoint.openInclusion X (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x.val))
  let r := CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (V).analyticSpace)
    (D).analyticSingularBoundaryᶜ
  have hr : Set.MapsTo r (Set.range (D).regularComplementInclusion)ᶜ (NX)ᶜ :=
    fun y hy => ((D).mem_regularThomComplement_iff y).mp hy
  let k := RelativeNeighborhoodPullback.neighborhoodSupportPairMap g (B) (SX)
    (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLiftAmbientMap_support X x.val)
    Set.univ Set.univ (fun _ _ => Set.mem_univ _)
  have hc : k ≫ (RelativeNeighborhoodPullback.neighborhoodToSubsetPair Set.univ (SX) ≫
      originalPointSupportPairMap X p x) =
    (RelativeNeighborhoodPullback.neighborhoodToSubsetPair Set.univ (B) ≫ RegularThomRelative.originalRegularAmbientPairMap X p x) ≫
      RelativeDualAbsoluteExtension.originalSubsetPairMap r hr := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl
  have ht : AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ (2 * p) (RelativeDualAbsoluteExtension.originalSubsetPairMap r hr)
      (RelativeSingularCochainBridge.relativeSingularCohomologyBridgeEquiv ℚ (TopCat.of (V).analyticSpace)
        (NX)ᶜ (2 * p) (NormalCoclassComparison.normalCoclassCoefficient p • (D).rationalSupportedCycleClass)) =
    RelativeSingularCochainBridge.relativeSingularCohomologyBridgeEquiv ℚ (TopCat.of (D).regularAmbientSpace)
      (Set.range (D).regularComplementInclusion)ᶜ (2 * p)
      (NormalCoclassComparison.normalCoclassCoefficient p • (D).regularThomClass) := by
    rw [← RelativeDualAbsoluteExtension.relativeSingularCohomologyBridgeEquiv_naturality]
    change RelativeSingularCochainBridge.relativeSingularCohomologyBridgeEquiv ℚ (TopCat.of (D).regularAmbientSpace)
      (Set.range (D).regularComplementInclusion)ᶜ (2 * p)
      ((D).regularThomCohomologyRestriction (ModuleCat.of ℚ ℚ) (2 * p)
        (NormalCoclassComparison.normalCoclassCoefficient p • (D).rationalSupportedCycleClass)) = _
    rw [map_smul, (D).rationalSupportedCycleClass_regularPullback]
  unfold originalSupportedCycleRelativeClass RegularThomRelative.originalRegularThomRelativeClass
  rw [← LinearMap.comp_apply, ← AlgebraicTopology.Singular.CohomologyTo.relativeCohomologyMap_comp, hc,
    AlgebraicTopology.Singular.CohomologyTo.relativeCohomologyMap_comp, LinearMap.comp_apply]
  simpa only using! congrArg (AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ (2 * p)
    (RelativeNeighborhoodPullback.neighborhoodToSubsetPair Set.univ (B) ≫ RegularThomRelative.originalRegularAmbientPairMap X p x)) ht

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SupportedCycleRelativeClass
