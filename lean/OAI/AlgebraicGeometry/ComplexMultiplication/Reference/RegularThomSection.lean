import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RegularThomRelative
import OAI.AlgebraicGeometry.ComplexMultiplication.TransportedNormalCoclass

/-! # Regular Thom Section -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RegularThomSection

noncomputable section

/-! # The actual regular Thom class gives the literal original smooth coclass section -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace OAI.AlgebraicTopology.Singular
open Opposite

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (p : ℕ) (x : CycleClassMap.OriginalCycleComponent X p)

local notation "V" => OAI.AlgebraicGeometry.ComplexMultiplication.BundledAbelianBridge.originalIntegralProjectiveVariety X
local notation "D" => OAI.AlgebraicGeometry.ComplexMultiplication.Reference.DimensionCycleSupports.originalDimensionSupport X p x
local notation "OX" => OAI.AlgebraicGeometry.Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpenOver X x.val
local notation "Y" => OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOver X x.val
local notation "i" => OAI.AlgebraicGeometry.Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLiftOver X x.val
local notation "B" => Set.range (OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map (i))

local instance CMOriginalRegularThomSection.localInstance1 : TopologicalSpace (V).analyticSpace :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.analyticTopology X
local instance CMOriginalRegularThomSection.localInstance2 : TopologicalSpace (D).regularAnalyticSpace :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.analyticTopology (D).regularOver

theorem originalRegularThomRelativeClass_section :
    (AlgebraicTopology.Support.RelativeCohomologySheaf.Singular.supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint (OX)))
      (B) (2 * p)).app (op ⊤) (RegularThomRelative.originalRegularThomRelativeClass X p x) =
    ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLiftCoclassSection X x.val x.property := by
  let := ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOver_hom_smoothOfRelativeDimension X x.val x.property
  apply RegularThomRelative.smoothSupportSection_of_relativeClass (OX) (Y) (i)
    (Topology.Dimension.Basic.TopologicalSpace.dim X.left - p) (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p
    (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLift_codimension X x.val x.property)
    (RegularThomRelative.originalRegularThomRelativeClass X p x)
  intro z
  let q := (RegularAmbientManifold.originalRegularCyclePointEquiv X p x).symm z
  have hq : RegularAmbientManifold.originalRegularCyclePoint X p x q = z :=
    (RegularAmbientManifold.originalRegularCyclePointEquiv X p x).apply_symm_apply z
  let W := RegularThomRelative.originalRegularThomChartOpen X p x q
  have hz : ComplexPoint.Basic.Point.map (i) z ∈ W := by
    rw [← hq]
    exact RegularThomRelative.originalRegularThomChartOpen_point X p x q
  have hW : W ≤ ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartOpen (OX) (Y) (i)
      (Topology.Dimension.Basic.TopologicalSpace.dim X.left - p) (Topology.Dimension.Basic.TopologicalSpace.dim X.left) z := by
    intro y hy
    have hs := RegularThomRelative.originalRegularThomChartOpen_source X p x q hy
    change y ∈ (RegularNormalCoordinates.originalRegularPaulNormalChart X p x q).source at hs
    simpa only [RegularNormalCoordinates.originalRegularPaulNormalChart, CMFlatteningCenteredTransport.transportFlatteningChart_source, hq] using! hs
  refine ⟨W, hz, hW, ?_⟩
  rw [RegularThomRelative.originalRegularThomRelativeClass_restrict]
  have he := TransportedNormalCoclass.transportedNormalCoclass_eq
    (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLift_codimension X x.val x.property)
    (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart (OX) (Y) (i)
      (Topology.Dimension.Basic.TopologicalSpace.dim X.left - p) (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (RegularAmbientManifold.originalRegularCyclePoint X p x q)) (B) W
    (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart_mem_range_iff (OX) (Y) (i)
      (Topology.Dimension.Basic.TopologicalSpace.dim X.left - p) (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (RegularAmbientManifold.originalRegularCyclePoint X p x q))
    (RegularNormalCoordinates.originalRegularPaulNormalChart_range X p x q)
    (by simpa only [hq] using! hW)
    (RegularThomRelative.originalRegularThomChartOpen_source X p x q)
  simpa only [RegularNormalCoordinates.originalRegularPaulNormalChart, ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartCoclass, hq] using! he

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RegularThomSection
