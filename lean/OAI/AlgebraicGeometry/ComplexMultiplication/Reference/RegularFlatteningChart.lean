import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RegularAmbientManifold
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.FlatteningDifferentiable

/-! # Regular Flattening Chart -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RegularFlatteningChart

noncomputable section

/-! # The literal original flattening chart on the native regular ambient open -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped _root_.Manifold

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (p : ℕ) (x : CycleClassMap.OriginalCycleComponent X p)

local notation "D" => OAI.AlgebraicGeometry.ComplexMultiplication.Reference.DimensionCycleSupports.originalDimensionSupport X p x
local notation "Y" => OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOver X x.val
local notation "OX" => OAI.AlgebraicGeometry.Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpenOver X x.val
local notation "i" => OAI.AlgebraicGeometry.Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLiftOver X x.val
local notation "h" => OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RegularAmbientManifold.originalRegularAmbientPointPartialHomeomorph X p x

local instance CMOriginalRegularFlatteningChart.localInstance1 : TopologicalSpace (BundledAbelianBridge.originalIntegralProjectiveVariety X).analyticSpace :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.analyticTopology X

local instance CMOriginalRegularFlatteningChart.localInstance2 : ChartedSpace
    (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
    (BundledAbelianBridge.originalIntegralProjectiveVariety X).analyticSpace :=
  ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeChartedSpace X

theorem originalRegularAmbientInverse_regularPoint (q : (D).regularAnalyticSpace) :
    (h).symm ((D).regularComplementInclusion q).val =
      ComplexPoint.Basic.Point.map (i) (RegularAmbientManifold.originalRegularCyclePoint X p x q) := by
  change (h).symm ((D).regularAnalyticToAmbient q) = _
  rw [← RegularAmbientManifold.originalRegularCyclePoint_ambient X p x q]
  exact (h).left_inv (by
    simp only [RegularAmbientManifold.originalRegularAmbientPointPartialHomeomorph,
      OpenChartRestriction.originalOpenImmersionPointPartialHomeomorph_source, Set.mem_univ])

theorem originalRegularAmbientInverse_support (u : (D).regularAmbientSpace) :
    (h).symm u.val ∈ Set.range (ComplexPoint.Basic.Point.map (i)) ↔
      u ∈ Set.range (D).regularComplementInclusion := by
  have hu : u.val ∈ (h).target := by
    rw [RegularAmbientManifold.originalRegularAmbientPointPartialHomeomorph_target]
    exact u.property
  have hc : ComplexPoint.Basic.Point.map (ComplexPoint.Basic.ComplexSchemePoint.openInclusion X (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x.val))
      ((h).symm u.val) = u.val := (h).right_inv hu
  rw [ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusClosedLift_complexPoints_range,
    (D).range_regularComplementInclusion, CycleSupport.originalDimensionSupport_analyticSupport X p x]
  change ComplexPoint.Basic.Point.map (ComplexPoint.Basic.ComplexSchemePoint.openInclusion X (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x.val))
      ((h).symm u.val) ∈ Cycle.Support.cycleComponentSupport X x.val ↔
    u.val ∈ Cycle.Support.cycleComponentSupport X x.val
  rw [hc]

/-- It is the original chart composed with the actual inverse open inclusion and subtype restriction. -/
def originalRegularFlatteningChart (q : (D).regularAnalyticSpace) :
    OpenPartialHomeomorph (D).regularAmbientSpace
      ((Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left - p) → ℂ) × (Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left - (Topology.Dimension.Basic.TopologicalSpace.dim X.left - p)) → ℂ)) :=
  letI := ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOver_hom_smoothOfRelativeDimension X x.val x.property
  ((h).symm.trans (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart
    (OX) (Y) (i) (Topology.Dimension.Basic.TopologicalSpace.dim X.left - p) (Topology.Dimension.Basic.TopologicalSpace.dim X.left)
    (RegularAmbientManifold.originalRegularCyclePoint X p x q))).subtypeRestr
      (inferInstance : Nonempty (D).regularAmbientSpace)

theorem originalRegularFlatteningChart_mem_source (q : (D).regularAnalyticSpace) :
    (D).regularComplementInclusion q ∈ (originalRegularFlatteningChart X p x q).source := by
  let := ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOver_hom_smoothOfRelativeDimension X x.val x.property
  change (D).regularComplementInclusion q ∈ (((h).symm.trans
    (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart (OX) (Y) (i)
      (Topology.Dimension.Basic.TopologicalSpace.dim X.left - p) (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (RegularAmbientManifold.originalRegularCyclePoint X p x q))).subtypeRestr
      (inferInstance : Nonempty (D).regularAmbientSpace)).source
  rw [OpenPartialHomeomorph.subtypeRestr_source, OpenPartialHomeomorph.trans_source]
  refine ⟨?_, ?_⟩
  · rw [OpenPartialHomeomorph.symm_source, RegularAmbientManifold.originalRegularAmbientPointPartialHomeomorph_target]
    exact ((D).regularComplementInclusion q).property
  · change (h).symm ((D).regularComplementInclusion q).val ∈
      (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart (OX) (Y) (i)
        (Topology.Dimension.Basic.TopologicalSpace.dim X.left - p) (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (RegularAmbientManifold.originalRegularCyclePoint X p x q)).source
    rw [originalRegularAmbientInverse_regularPoint]
    exact ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart_mem_source _ _ _ _ _ _

theorem originalRegularFlatteningChart_range (q : (D).regularAnalyticSpace)
    (u : (D).regularAmbientSpace)
    (hu : u ∈ (originalRegularFlatteningChart X p x q).source) :
    u ∈ Set.range (D).regularComplementInclusion ↔
      (originalRegularFlatteningChart X p x q u).2 = 0 := by
  let := ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOver_hom_smoothOfRelativeDimension X x.val x.property
  change u ∈ (((h).symm.trans
    (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart (OX) (Y) (i)
      (Topology.Dimension.Basic.TopologicalSpace.dim X.left - p) (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (RegularAmbientManifold.originalRegularCyclePoint X p x q))).subtypeRestr
      (inferInstance : Nonempty (D).regularAmbientSpace)).source at hu
  rw [OpenPartialHomeomorph.subtypeRestr_source, OpenPartialHomeomorph.trans_source] at hu
  change u ∈ Set.range (D).regularComplementInclusion ↔
    (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart (OX) (Y) (i)
      (Topology.Dimension.Basic.TopologicalSpace.dim X.left - p) (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (RegularAmbientManifold.originalRegularCyclePoint X p x q)
      ((h).symm u.val)).2 = 0
  have hu' : (h).symm u.val ∈ (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart
      (OX) (Y) (i) (Topology.Dimension.Basic.TopologicalSpace.dim X.left - p) (Topology.Dimension.Basic.TopologicalSpace.dim X.left)
      (RegularAmbientManifold.originalRegularCyclePoint X p x q)).source := hu.2
  exact (originalRegularAmbientInverse_support X p x u).symm.trans
    (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart_mem_range_iff _ _ _ _ _ _ _ hu')

theorem originalRegularFlatteningChart_mDifferentiable (q : (D).regularAnalyticSpace) :
    (originalRegularFlatteningChart X p x q).MDifferentiable
      𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
      𝓘(ℂ, (Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left - p) → ℂ) ×
        (Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left - (Topology.Dimension.Basic.TopologicalSpace.dim X.left - p)) → ℂ)) := by
  let := ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOver_hom_smoothOfRelativeDimension X x.val x.property
  have hh : (h).MDifferentiable 𝓘(ℂ, Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)
      𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) := by
    have hh0 := OpenChartRestriction.originalOpenImmersionPointPartialHomeomorph_mDifferentiable
        (ComplexPoint.Basic.ComplexSchemePoint.openInclusion X (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x.val))
    change (h).MDifferentiable 𝓘(ℂ, Fin (Topology.Dimension.Basic.TopologicalSpace.dim (OX).left) → ℂ)
      𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) at hh0
    have transfer (d : ℕ) (hd : Topology.Dimension.Basic.TopologicalSpace.dim (OX).left = d) :
        let _ : SmoothOfRelativeDimension d (OX).hom :=
          hd ▸ (inferInstanceAs (SmoothOfRelativeDimension (Topology.Dimension.Basic.TopologicalSpace.dim (OX).left) (OX).hom))
        (h).MDifferentiable 𝓘(ℂ, Fin d → ℂ)
          𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) := by
      subst d
      exact hh0
    exact transfer (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (RegularAmbientManifold.originalRegularAmbientDimension X p x)
  exact OpenChartRestriction.complexChart_subtypeRestr_mDifferentiable _
    (hh.symm.trans (FlatteningDifferentiable.originalFlatteningChart_mDifferentiable _ _ _ _ _ _)) _ _

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RegularFlatteningChart
