import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RegularAmbientHomeomorph
import OAI.AlgebraicGeometry.ComplexMultiplication.CMFlatteningCenteredTransport

/-! # Regular Normal Coordinates -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RegularNormalCoordinates

noncomputable section

/-! # The actual native and original normal coordinates agree under the actual open homeomorphism -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace

theorem transportedNormalCoordinates_eq
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N] {m n r p : ℕ}
    (hm : m = r) (hn : n = p)
    (e : OpenPartialHomeomorph M ((Fin m → ℂ) × (Fin n → ℂ)))
    (d : OpenPartialHomeomorph N ((Fin m → ℂ) × (Fin n → ℂ)))
    (a : M) (b : N) (hc : (e a).2 = (d b).2) :
    (CMFlatteningCenteredTransport.transportFlatteningChart hm hn e a).2 =
      (CMFlatteningCenteredTransport.transportFlatteningChart rfl hn d b).2 := by
  subst r p
  exact hc

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (p : ℕ) (x : CycleClassMap.OriginalCycleComponent X p)

local notation "V" => OAI.AlgebraicGeometry.ComplexMultiplication.BundledAbelianBridge.originalIntegralProjectiveVariety X
local notation "D" => OAI.AlgebraicGeometry.ComplexMultiplication.Reference.DimensionCycleSupports.originalDimensionSupport X p x
local notation "Y" => OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOver X x.val
local notation "OX" => OAI.AlgebraicGeometry.Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpenOver X x.val
local notation "i" => OAI.AlgebraicGeometry.Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLiftOver X x.val
local notation "H" => OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RegularAmbientHomeomorph.originalRegularAmbientHomeomorph X p x

local instance CMOriginalRegularNormalCoordinates.localInstance1 : TopologicalSpace (V).analyticSpace :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.analyticTopology X
local instance CMOriginalRegularNormalCoordinates.localInstance2 : TopologicalSpace (D).regularAnalyticSpace :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.analyticTopology (D).regularOver

/-- The literal original holomorphic chart, with only its proved normal dimension equality transported. -/
def originalRegularPaulNormalChart (q : (D).regularAnalyticSpace) :
    OpenPartialHomeomorph (ComplexPoint.Basic.ComplexSchemePoint (OX)) ((Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left - p) → ℂ) × (Fin p → ℂ)) :=
  letI := ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOver_hom_smoothOfRelativeDimension X x.val x.property
  CMFlatteningCenteredTransport.transportFlatteningChart rfl
    (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLift_codimension X x.val x.property)
    (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart (OX) (Y) (i)
      (Topology.Dimension.Basic.TopologicalSpace.dim X.left - p) (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (RegularAmbientManifold.originalRegularCyclePoint X p x q))

theorem originalRegularNormalCoordinates_eq (q : (D).regularAnalyticSpace)
    (u : (D).regularAmbientSpace) :
    (RegularAmbientHomeomorph.originalRegularNormalChart X p x q u).2 =
      (originalRegularPaulNormalChart X p x q ((H).symm u)).2 := by
  let := ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOver_hom_smoothOfRelativeDimension X x.val x.property
  unfold RegularAmbientHomeomorph.originalRegularNormalChart originalRegularPaulNormalChart
  apply transportedNormalCoordinates_eq
  change (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart (OX) (Y) (i)
      (Topology.Dimension.Basic.TopologicalSpace.dim X.left - p) (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (RegularAmbientManifold.originalRegularCyclePoint X p x q)
      ((RegularAmbientManifold.originalRegularAmbientPointPartialHomeomorph X p x).symm u.val)).2 = _
  rw [← RegularAmbientHomeomorph.originalRegularAmbientHomeomorph_symm_apply]

theorem originalRegularPaulNormalChart_range (q : (D).regularAnalyticSpace)
    (y : ComplexPoint.Basic.ComplexSchemePoint (OX)) (hy : y ∈ (originalRegularPaulNormalChart X p x q).source) :
    y ∈ Set.range (ComplexPoint.Basic.Point.map (i)) ↔ (originalRegularPaulNormalChart X p x q y).2 = 0 := by
  let := ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOver_hom_smoothOfRelativeDimension X x.val x.property
  have hy' : y ∈ (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart (OX) (Y) (i)
      (Topology.Dimension.Basic.TopologicalSpace.dim X.left - p) (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (RegularAmbientManifold.originalRegularCyclePoint X p x q)).source := by
    simpa only [originalRegularPaulNormalChart, CMFlatteningCenteredTransport.transportFlatteningChart_source] using! hy
  exact (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart_mem_range_iff _ _ _ _ _ _ _ hy').trans
    (CMFlatteningCenteredTransport.transportFlatteningChart_normal_zero rfl
      (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLift_codimension X x.val x.property) _ y).symm

theorem originalRegularPaulNormalChart_inverse_mem_source (q : (D).regularAnalyticSpace)
    (u : (D).regularAmbientSpace) (hu : u ∈ (RegularAmbientHomeomorph.originalRegularNormalChart X p x q).source) :
    (H).symm u ∈ (originalRegularPaulNormalChart X p x q).source := by
  let := ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOver_hom_smoothOfRelativeDimension X x.val x.property
  have hu' : u ∈ (RegularFlatteningChart.originalRegularFlatteningChart X p x q).source := by
    simpa only [RegularAmbientHomeomorph.originalRegularNormalChart, CMFlatteningCenteredTransport.transportFlatteningChart_source] using! hu
  change u ∈ (((RegularAmbientManifold.originalRegularAmbientPointPartialHomeomorph X p x).symm.trans
    (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart (OX) (Y) (i)
      (Topology.Dimension.Basic.TopologicalSpace.dim X.left - p) (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (RegularAmbientManifold.originalRegularCyclePoint X p x q))).subtypeRestr
      (inferInstance : Nonempty (D).regularAmbientSpace)).source at hu'
  rw [OpenPartialHomeomorph.subtypeRestr_source, OpenPartialHomeomorph.trans_source] at hu'
  have hx := hu'.2
  change (RegularAmbientManifold.originalRegularAmbientPointPartialHomeomorph X p x).symm u.val ∈
    (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart (OX) (Y) (i)
      (Topology.Dimension.Basic.TopologicalSpace.dim X.left - p) (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (RegularAmbientManifold.originalRegularCyclePoint X p x q)).source at hx
  rw [← RegularAmbientHomeomorph.originalRegularAmbientHomeomorph_symm_apply] at hx
  simpa only [originalRegularPaulNormalChart, CMFlatteningCenteredTransport.transportFlatteningChart_source] using! hx

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RegularNormalCoordinates
