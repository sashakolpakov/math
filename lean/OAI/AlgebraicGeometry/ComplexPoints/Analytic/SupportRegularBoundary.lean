import OAI.AlgebraicGeometry.ComplexPoints.Analytic.StratumNormalSpace
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemeImmersionPointTopology
import OAI.AlgebraicGeometry.CycleClass.Geometric.StratumDimension

/-! # Support Regular Boundary -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-!
# The actual singular boundary of a cycle support

The nonsmooth boundary is a closed analytic subset. Its complement inside the
support is exactly the image of the native smooth-locus point map. These set
identities use the actual residue-field lifting theorem for immersion images.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

/-- The genuine underlying point, with its codomain written as the variety's
carrier so that subsequent set identities do not depend on an over-object projection. -/
abbrev Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.analyticUnderlying (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    V.analyticSpace → V.carrier :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (X := V.toOver)

theorem Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.continuous_analyticUnderlying
    (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : Continuous V.analyticUnderlying :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_underlying

/-- The algebraic singular boundary is exactly the support minus the image
of its actual smooth open locus. -/
theorem ComplexPoints.Analytic.SupportRegularBoundary.supportSingularBoundary_eq_sdiff {X : Scheme} (Z : IrreducibleCloseds X)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] :
    CycleClass.Geometric.StratumDimension.supportSingularBoundary Z f =
      (Z : Set X) \ Set.range (CycleClass.Geometric.SmoothStratum.reducedSupportSmoothStratumι Z (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← CycleClass.Geometric.GenericPoint.range_reducedSupportι Z]
      exact Set.mem_range_self x
    · rintro ⟨z, hz⟩
      have he : CycleClass.Geometric.SmoothStratum.smoothStratumι (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f) z = x :=
        (CycleClass.Geometric.GenericPoint.reducedSupportι Z).isClosedEmbedding.injective hz
      have hreg : x ∈ Set.range (CycleClass.Geometric.SmoothStratum.smoothStratumι (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f)) := ⟨z, he⟩
      rw [CycleClass.Geometric.SmoothStratum.range_smoothStratumι] at hreg
      exact hx hreg
  · rintro ⟨hy, hnot⟩
    have hyrange : y ∈ Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι Z) := by
      simpa only [CycleClass.Geometric.GenericPoint.range_reducedSupportι] using hy
    obtain ⟨x, rfl⟩ := hyrange
    refine ⟨x, ?_, rfl⟩
    intro hx
    exact hnot ⟨⟨x, hx⟩, rfl⟩

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}

local instance CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.ambientLocallyOfFiniteType : LocallyOfFiniteType V.structureMap := by
  let : Smooth V.structureMap := V.presentation.smooth
  infer_instance

/-- The existing smooth-locus point map into the actual analytic variety. -/
abbrev CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAnalyticToAmbient (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Z.regularAnalyticSpace → V.analyticSpace := Z.regularAmbientInclusion

theorem CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.isEmbedding_regularAnalyticToAmbient (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Topology.IsEmbedding Z.regularAnalyticToAmbient :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion Z.regularToAmbient

theorem CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.continuous_regularAnalyticToAmbient (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Continuous Z.regularAnalyticToAmbient :=
  Z.isEmbedding_regularAnalyticToAmbient.continuous

/-- The actual analytic points above the algebraic singular boundary. -/
def CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.analyticSingularBoundary (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) : Set V.analyticSpace :=
  V.analyticUnderlying ⁻¹' CycleClass.Geometric.StratumDimension.supportSingularBoundary Z.1 V.structureMap

theorem CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.isClosed_analyticSingularBoundary (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    IsClosed Z.analyticSingularBoundary :=
  (CycleClass.Geometric.StratumDimension.isClosed_supportSingularBoundary Z.1 V.structureMap).preimage
    V.continuous_analyticUnderlying

/-- Exact support-point membership, including the residue-field lifting direction. -/
theorem CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.range_analyticInclusion (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Set.range Z.analyticInclusion =
      V.analyticUnderlying ⁻¹' (Z.1 : Set V.carrier) := by
  let : IsClosedImmersion Z.toAmbient.left := Z.inclusion_isClosedImmersion
  calc
    Set.range Z.analyticInclusion = V.analyticUnderlying ⁻¹' Set.range Z.inclusion :=
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isImmersion Z.toAmbient
    _ = V.analyticUnderlying ⁻¹' (Z.1 : Set V.carrier) :=
      congrArg (fun S : Set V.carrier => V.analyticUnderlying ⁻¹' S)
        (CycleClass.Geometric.GenericPoint.range_reducedSupportι Z.1)

/-- Exact smooth-locus point membership for the genuine immersion. -/
theorem CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.range_regularAnalyticToAmbient (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Set.range Z.regularAnalyticToAmbient =
      V.analyticUnderlying ⁻¹'
        Set.range (CycleClass.Geometric.SmoothStratum.reducedSupportSmoothStratumι Z.1 Z.structureMap) :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isImmersion Z.regularToAmbient

/-- The analytic singular boundary is precisely what the smooth locus omits. -/
theorem CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.analyticSingularBoundary_eq_sdiff (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Z.analyticSingularBoundary =
      Set.range Z.analyticInclusion \ Set.range Z.regularAnalyticToAmbient := by
  rw [Z.range_analyticInclusion, Z.range_regularAnalyticToAmbient]
  change V.analyticUnderlying ⁻¹' CycleClass.Geometric.StratumDimension.supportSingularBoundary Z.1 V.structureMap = _
  rw [ComplexPoints.Analytic.SupportRegularBoundary.supportSingularBoundary_eq_sdiff, Set.preimage_sdiff]

theorem CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.range_regularAnalyticToAmbient_subset (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Set.range Z.regularAnalyticToAmbient ⊆ Set.range Z.analyticInclusion := by
  rintro _ ⟨x, rfl⟩
  exact ⟨Z.regularAnalyticInclusion x, rfl⟩

theorem CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.analyticSingularBoundary_subset_range (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Z.analyticSingularBoundary ⊆ Set.range Z.analyticInclusion := by
  rw [Z.analyticSingularBoundary_eq_sdiff]
  exact Set.sdiff_subset

theorem CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAnalyticToAmbient_not_mem_boundary (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) : Z.regularAnalyticToAmbient x ∉ Z.analyticSingularBoundary := by
  rw [Z.analyticSingularBoundary_eq_sdiff]
  exact fun hx => hx.2 (Set.mem_range_self x)

/-- Removing the closed singular boundary from the support leaves exactly
the analytic smooth-locus image. -/
theorem CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.range_analyticInclusion_sdiff_boundary (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Set.range Z.analyticInclusion \ Z.analyticSingularBoundary =
      Set.range Z.regularAnalyticToAmbient := by
  rw [Z.analyticSingularBoundary_eq_sdiff]
  exact Set.sdiff_sdiff_cancel_left (Z.range_regularAnalyticToAmbient_subset)

/-- Both parts cover the actual analytic support. -/
theorem CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regular_union_boundary (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Set.range Z.regularAnalyticToAmbient ∪ Z.analyticSingularBoundary =
      Set.range Z.analyticInclusion := by
  rw [Z.analyticSingularBoundary_eq_sdiff]
  exact Set.union_sdiff_cancel (Z.range_regularAnalyticToAmbient_subset)

end

end OAI.AlgebraicGeometry
