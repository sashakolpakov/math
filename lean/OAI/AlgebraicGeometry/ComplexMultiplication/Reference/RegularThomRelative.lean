import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RegularNormalCoordinates
import OAI.AlgebraicGeometry.ComplexMultiplication.IntrinsicRelativeNeighborhoodNormalization
import OAI.AlgebraicGeometry.Cycle.SmoothPairGerm

/-! # Regular Thom Relative -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RegularThomRelative

noncomputable section

section

/-! # The genuine regular Thom class in the original ambient open -/

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
local notation "H" => OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RegularAmbientHomeomorph.originalRegularAmbientHomeomorph X p x
local notation "B" => Set.range (OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map (i))
local notation "S" => Set.range (OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularComplementInclusion
  (DimensionCycleSupports.originalDimensionSupport X p x))

local instance CMOriginalRegularThomRelativeClass.localInstance1 : TopologicalSpace (V).analyticSpace :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.analyticTopology X
local instance CMOriginalRegularThomRelativeClass.localInstance2 : TopologicalSpace (D).regularAnalyticSpace :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.analyticTopology (D).regularOver

/-- This map is the actual open-immersion homeomorphism on both parts of the pair. -/
def originalRegularAmbientPairMap :
    TopPair.ofSubset (X := TopCat.of (ComplexPoint.Basic.ComplexSchemePoint (OX))) (B)ᶜ ⟶
      TopPair.ofSubset (X := TopCat.of (D).regularAmbientSpace) (S)ᶜ :=
  RelativeDualAbsoluteExtension.originalSubsetPairMap (TopCat.ofHom ⟨(H), (H).continuous⟩) (by
    intro y hy
    change (H) y ∉ (S)
    intro h
    exact hy ((congrArg (fun T : Set (ComplexPoint.Basic.ComplexSchemePoint (OX)) => y ∈ T)
      (RegularAmbientHomeomorph.originalRegularAmbientHomeomorph_support X p x)).mp h))

/-- Pullback of the actual regular Thom class, with the fixed nonzero normalizing scalar. -/
def originalRegularThomRelativeClass :
    AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ
      (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (Set.univ : Set (ComplexPoint.Basic.ComplexSchemePoint (OX))) (B)) (2 * p) :=
  AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ (2 * p)
    (RelativeNeighborhoodPullback.neighborhoodToSubsetPair Set.univ (B) ≫ originalRegularAmbientPairMap X p x)
    (RelativeSingularCochainBridge.relativeSingularCohomologyBridgeEquiv ℚ (TopCat.of (D).regularAmbientSpace)
      (S)ᶜ (2 * p) (NormalCoclassComparison.normalCoclassCoefficient p • (D).regularThomClass))

/-- The inverse image of the actual normal product neighborhood. -/
def originalRegularThomChartOpen (q : (D).regularAnalyticSpace) :
    Opens (ComplexPoint.Basic.ComplexSchemePoint (OX)) :=
  ⟨(H) ⁻¹' (RegularAmbientHomeomorph.originalRegularNormalPair X p x q).neighborhood,
    (RegularAmbientHomeomorph.originalRegularNormalPair X p x q).isOpen_neighborhood.preimage (H).continuous⟩

theorem originalRegularAmbientHomeomorph_regularPoint (q : (D).regularAnalyticSpace) :
    (H) (ComplexPoint.Basic.Point.map (i) (RegularAmbientManifold.originalRegularCyclePoint X p x q)) =
      (D).regularComplementInclusion q := by
  apply (H).symm.injective
  rw [(H).symm_apply_apply, RegularAmbientHomeomorph.originalRegularAmbientHomeomorph_symm_apply]
  exact (RegularFlatteningChart.originalRegularAmbientInverse_regularPoint X p x q).symm

theorem originalRegularThomChartOpen_point (q : (D).regularAnalyticSpace) :
    ComplexPoint.Basic.Point.map (i) (RegularAmbientManifold.originalRegularCyclePoint X p x q) ∈
      originalRegularThomChartOpen X p x q := by
  change (H) (ComplexPoint.Basic.Point.map (i) (RegularAmbientManifold.originalRegularCyclePoint X p x q)) ∈
    (RegularAmbientHomeomorph.originalRegularNormalPair X p x q).neighborhood
  rw [originalRegularAmbientHomeomorph_regularPoint]
  exact (RegularAmbientHomeomorph.originalRegularNormalPair X p x q).point_mem_neighborhood

theorem originalRegularThomChartOpen_source (q : (D).regularAnalyticSpace) :
    (originalRegularThomChartOpen X p x q : Set (ComplexPoint.Basic.ComplexSchemePoint (OX))) ⊆
      (RegularNormalCoordinates.originalRegularPaulNormalChart X p x q).source := by
  intro y hy
  have hs := (RegularAmbientHomeomorph.originalRegularNormalPair X p x q).neighborhood_subset_source hy
  change (H) y ∈ (CenteredFlatteningNormalPair.centeredFlatteningChart (D).regularComplementInclusion q
    (RegularAmbientHomeomorph.originalRegularNormalChart X p x q)).source at hs
  rw [CenteredFlatteningNormalPair.centeredFlatteningChart_source] at hs
  have ht := RegularNormalCoordinates.originalRegularPaulNormalChart_inverse_mem_source X p x q ((H) y) hs
  rwa [(H).symm_apply_apply] at ht

end

section

/-! # Local normalization of the genuine global regular Thom class -/

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
local notation "H" => OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RegularAmbientHomeomorph.originalRegularAmbientHomeomorph X p x
local notation "B" => Set.range (OAI.AlgebraicGeometry.ComplexPoint.Basic.Point.map (i))
local notation "S" => Set.range (OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularComplementInclusion
  (DimensionCycleSupports.originalDimensionSupport X p x))

local instance CMOriginalRegularThomLocalPullback.localInstance1 : TopologicalSpace (V).analyticSpace :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.analyticTopology X
local instance CMOriginalRegularThomLocalPullback.localInstance2 : TopologicalSpace (D).regularAnalyticSpace :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.analyticTopology (D).regularOver

theorem originalRegularThomRelativeClass_restrict (q : (D).regularAnalyticSpace) :
    AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ (2 * p)
      (AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.neighborhoodSupportInclusionPairMap (Set.subset_univ
        (originalRegularThomChartOpen X p x q : Set (ComplexPoint.Basic.ComplexSchemePoint (OX)))) (B))
      (originalRegularThomRelativeClass X p x) =
    AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.chartNormalProjectionCoclass (Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left - p) → ℂ) p
      (RegularNormalCoordinates.originalRegularPaulNormalChart X p x q) (B)
      (RegularNormalCoordinates.originalRegularPaulNormalChart_range X p x q)
      (originalRegularThomChartOpen X p x q : Set (ComplexPoint.Basic.ComplexSchemePoint (OX)))
      (originalRegularThomChartOpen_source X p x q) := by
  let P := RegularAmbientHomeomorph.originalRegularNormalPair X p x q
  let W : Set (ComplexPoint.Basic.ComplexSchemePoint (OX)) := originalRegularThomChartOpen X p x q
  let f : C(ComplexPoint.Basic.ComplexSchemePoint (OX), (D).regularAmbientSpace) := ⟨(H), (H).continuous⟩
  have hWU : Set.MapsTo f W P.neighborhood := fun _ hy => hy
  let k := RelativeNeighborhoodPullback.neighborhoodSupportPairMap f (B) (S)
    (RegularAmbientHomeomorph.originalRegularAmbientHomeomorph_support X p x) W P.neighborhood hWU
  have hc : AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.neighborhoodSupportInclusionPairMap (Set.subset_univ W) (B) ≫
      (RelativeNeighborhoodPullback.neighborhoodToSubsetPair Set.univ (B) ≫ originalRegularAmbientPairMap X p x) =
    k ≫ RelativeNeighborhoodPullback.neighborhoodToSubsetPair P.neighborhood (S) := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl
  have hnorm : AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ (2 * p)
      (RelativeNeighborhoodPullback.neighborhoodToSubsetPair P.neighborhood (S))
      (RelativeSingularCochainBridge.relativeSingularCohomologyBridgeEquiv ℚ (TopCat.of (D).regularAmbientSpace)
        (S)ᶜ (2 * p) (NormalCoclassComparison.normalCoclassCoefficient p • (D).regularThomClass)) =
    FlatteningNormalCoclassComparison.originalCenteredNormalPairCoclass p (D).regularComplementInclusion q
      (RegularAmbientHomeomorph.originalRegularNormalChart X p x q)
      (RegularAmbientHomeomorph.originalRegularNormalChart_mem_source X p x q)
      (RegularAmbientHomeomorph.originalRegularNormalChart_normal_center X p x q)
      (RegularAmbientHomeomorph.originalRegularNormalChart_range X p x q) := by
    exact (IntrinsicRelativeNeighborhoodNormalization.nativeRelativeNeighborhood_normalization ℚ (TopCat.of (D).regularAmbientSpace)
      (S) P.openNeighborhood (2 * p)
      (NormalCoclassComparison.normalCoclassCoefficient p • (D).regularThomClass)).symm.trans
        (RegularAmbientHomeomorph.originalRegularThomClass_local_comparison X p x q)
  have hU : P.neighborhood ⊆ (RegularAmbientHomeomorph.originalRegularNormalChart X p x q).source := by
    intro u hu
    have hs := P.neighborhood_subset_source hu
    change u ∈ (CenteredFlatteningNormalPair.centeredFlatteningChart (D).regularComplementInclusion q
      (RegularAmbientHomeomorph.originalRegularNormalChart X p x q)).source at hs
    rwa [CenteredFlatteningNormalPair.centeredFlatteningChart_source] at hs
  unfold originalRegularThomRelativeClass
  rw [← LinearMap.comp_apply, ← AlgebraicTopology.Singular.CohomologyTo.relativeCohomologyMap_comp, hc,
    AlgebraicTopology.Singular.CohomologyTo.relativeCohomologyMap_comp, LinearMap.comp_apply, hnorm]
  apply RelativeNeighborhoodPullback.chartNormalCoclass_pullback p f (B) (S)
    (RegularAmbientHomeomorph.originalRegularAmbientHomeomorph_support X p x)
    (RegularNormalCoordinates.originalRegularPaulNormalChart X p x q) (RegularAmbientHomeomorph.originalRegularNormalChart X p x q)
    (RegularNormalCoordinates.originalRegularPaulNormalChart_range X p x q)
    (RegularAmbientHomeomorph.originalRegularNormalChart_range X p x q) W P.neighborhood hWU
    (originalRegularThomChartOpen_source X p x q) hU
  intro y hy
  have he := RegularNormalCoordinates.originalRegularNormalCoordinates_eq X p x q ((H) y)
  rw [(H).symm_apply_apply] at he
  exact he.symm

end

/-! # Recognizing the original glued coclass by its actual local relative classes -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace OAI.AlgebraicTopology.Singular
open Opposite

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace

variable (X Y : Over (Spec (.of ℂ))) (i : Y ⟶ X) (m d p : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left]

theorem smoothSupportSection_of_relativeClass (hp : d - m = p)
    (a : AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair
      (Set.univ : Set (ComplexPoint.Basic.ComplexSchemePoint X)) (Set.range (ComplexPoint.Basic.Point.map i))) (2 * p))
    (hl : ∀ z : ComplexPoint.Basic.ComplexSchemePoint Y, ∃ (W : Opens (ComplexPoint.Basic.ComplexSchemePoint X))
      (_ : ComplexPoint.Basic.Point.map i z ∈ W)
      (hW : W ≤ ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartOpen X Y i m d z),
      AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ (2 * p)
        (AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.neighborhoodSupportInclusionPairMap (Set.subset_univ (W : Set (ComplexPoint.Basic.ComplexSchemePoint X)))
          (Set.range (ComplexPoint.Basic.Point.map i))) a =
        hp ▸ ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartCoclass X Y i m d z W hW) :
    (AlgebraicTopology.Support.RelativeCohomologySheaf.Singular.supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
      (Set.range (ComplexPoint.Basic.Point.map i)) (2 * p)).app (op ⊤) a =
    hp ▸ ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassSection X Y i m d := by
  subst p
  apply TopCat.Presheaf.section_ext
    (AlgebraicTopology.Support.RelativeCohomologySheaf.Singular.supportRelativeCohomologySheaf (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
      (Set.range (ComplexPoint.Basic.Point.map i)) (2 * (d - m))) ⊤
  intro y hy
  change AlgebraicTopology.Support.RelativeCohomologySheaf.Singular.supportRelativeCohomologyGerm (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
    (Set.range (ComplexPoint.Basic.Point.map i)) (2 * (d - m)) ⊤ y hy a =
    (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassSheaf X Y i m d).presheaf.Γgerm y
      (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassSection X Y i m d)
  rw [ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassSection_germ]
  by_cases hs : y ∈ Set.range (ComplexPoint.Basic.Point.map i)
  · obtain ⟨z, rfl⟩ := hs
    obtain ⟨W, hz, hW, he⟩ := hl z
    rw [ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassStalk_eq_chartGerm X Y i m d z _
      (ComplexPoint.Basic.ComplexSchemePoint.mem_smoothClosedSupportChartOpen X Y i m d z)]
    apply AlgebraicTopology.Support.RelativeCohomologyEq.Singular.supportRelativeCohomologyGerm_eq_of_restrict_eq
      (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) (Set.range (ComplexPoint.Basic.Point.map i)) (2 * (d - m))
      (U := ⊤) (V := ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartOpen X Y i m d z)
      (le_top) hW (ComplexPoint.Basic.Point.map i z) hz
    simpa only [ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartCoclass_restrict] using! he
  · rw [AlgebraicTopology.Support.RelativeCohomologyEq.Singular.supportRelativeCohomologyGerm_eq_zero_of_not_mem
      (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) (Set.range (ComplexPoint.Basic.Point.map i)) (2 * (d - m))
      (ComplexPoint.Basic.ComplexSchemePoint.isClosed_range_map_of_closedImmersion i) ⊤ y hy hs a,
      ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassStalk_eq_zero X Y i m d y hs]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RegularThomRelative
