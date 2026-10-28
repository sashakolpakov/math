import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RegularFlatteningChart
import OAI.AlgebraicGeometry.ComplexMultiplication.CMFlatteningCenteredTransport
import OAI.AlgebraicGeometry.ComplexMultiplication.FlatteningNormalCoclassComparison
import OAI.AlgebraicGeometry.CycleClass.Geometric.RegularThom

/-! # Regular Ambient Homeomorph -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RegularAmbientHomeomorph

noncomputable section

section

/-! # The actual original normal chart is a normal pair for the native Thom class -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace OAI.AlgebraicTopology.Singular
open scoped _root_.Manifold

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (p : ℕ) (x : CycleClassMap.OriginalCycleComponent X p)

local notation "V" => OAI.AlgebraicGeometry.ComplexMultiplication.BundledAbelianBridge.originalIntegralProjectiveVariety X
local notation "D" => OAI.AlgebraicGeometry.ComplexMultiplication.Reference.DimensionCycleSupports.originalDimensionSupport X p x

local instance CMOriginalRegularNormalPair.localInstance1 : TopologicalSpace (V).analyticSpace :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.analyticTopology X
local instance CMOriginalRegularNormalPair.localInstance2 : ChartedSpace (V).analyticModel (V).analyticSpace :=
  ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeChartedSpace X
local instance CMOriginalRegularNormalPair.localInstance3 : TopologicalSpace (D).regularAnalyticSpace :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.analyticTopology (D).regularOver

/-- The same actual original chart, using the already proved equal model dimensions. -/
def originalRegularNormalChart (q : (D).regularAnalyticSpace) :
    OpenPartialHomeomorph (D).regularAmbientSpace ((D).regularAnalyticModel × (Fin p → ℂ)) :=
  CMFlatteningCenteredTransport.transportFlatteningChart (RegularAmbientManifold.originalRegularCycleModelDimension X p x).symm
    (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLift_codimension X x.val x.property)
    (RegularFlatteningChart.originalRegularFlatteningChart X p x q)

theorem originalRegularNormalChart_mem_source (q : (D).regularAnalyticSpace) :
    (D).regularComplementInclusion q ∈ (originalRegularNormalChart X p x q).source := by
  simpa only [originalRegularNormalChart, CMFlatteningCenteredTransport.transportFlatteningChart_source] using!
    RegularFlatteningChart.originalRegularFlatteningChart_mem_source X p x q

theorem originalRegularNormalChart_range (q : (D).regularAnalyticSpace)
    (u : (D).regularAmbientSpace) (hu : u ∈ (originalRegularNormalChart X p x q).source) :
    u ∈ Set.range (D).regularComplementInclusion ↔
      (originalRegularNormalChart X p x q u).2 = 0 := by
  have hu' : u ∈ (RegularFlatteningChart.originalRegularFlatteningChart X p x q).source := by
    simpa only [originalRegularNormalChart, CMFlatteningCenteredTransport.transportFlatteningChart_source] using! hu
  exact (RegularFlatteningChart.originalRegularFlatteningChart_range X p x q u hu').trans
    (CMFlatteningCenteredTransport.transportFlatteningChart_normal_zero
      (RegularAmbientManifold.originalRegularCycleModelDimension X p x).symm
      (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLift_codimension X x.val x.property) _ u).symm

theorem originalRegularNormalChart_normal_center (q : (D).regularAnalyticSpace) :
    (originalRegularNormalChart X p x q ((D).regularComplementInclusion q)).2 = 0 :=
  (originalRegularNormalChart_range X p x q _
    (originalRegularNormalChart_mem_source X p x q)).mp ⟨q, rfl⟩

/-- The normal pair centers only the tangential coordinate of that actual chart. -/
def originalRegularNormalPair (q : (D).regularAnalyticSpace) :
    ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (D).regularAnalyticModel (Fin p → ℂ)
      (D).regularComplementInclusion q :=
  CenteredFlatteningNormalPair.centeredFlatteningNormalPair (D).regularComplementInclusion q
    (originalRegularNormalChart X p x q)
    (originalRegularNormalChart_mem_source X p x q)
    (originalRegularNormalChart_normal_center X p x q)
    (originalRegularNormalChart_range X p x q)

theorem originalRegularNormalPair_mDifferentiable (q : (D).regularAnalyticSpace) :
    (originalRegularNormalPair X p x q).ambientChart.MDifferentiable
      𝓘(ℂ, (V).analyticModel) 𝓘(ℂ, (D).regularAnalyticModel × (Fin p → ℂ)) := by
  apply CMFlatteningCenteredTransport.centeredFlatteningChart_mDifferentiable
  exact CMFlatteningCenteredTransport.transportFlatteningChart_mDifferentiable _ _ _
    (RegularFlatteningChart.originalRegularFlatteningChart_mDifferentiable X p x q)

local notation "P" q => OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RegularAmbientHomeomorph.originalRegularNormalPair X p x q

theorem originalRegularThomClass_local_comparison (q : (D).regularAnalyticSpace) :
    RelativeSingularCochainBridge.relativeSingularCohomologyBridgeEquiv ℚ (TopCat.of (P q).neighborhood)
      (P q).relativeComplement (2 * p)
      (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ)
        (TopCat.of (D).regularAmbientSpace) (Set.range (D).regularComplementInclusion)ᶜ
        (P q).openNeighborhood (2 * p)
        (NormalCoclassComparison.normalCoclassCoefficient p • (D).regularThomClass)) =
    FlatteningNormalCoclassComparison.originalCenteredNormalPairCoclass p (D).regularComplementInclusion q
      (originalRegularNormalChart X p x q)
      (originalRegularNormalChart_mem_source X p x q)
      (originalRegularNormalChart_normal_center X p x q)
      (originalRegularNormalChart_range X p x q) := by
  have ht := (D).regularThomClass_restrict_normalPair q (P q)
    (originalRegularNormalPair_mDifferentiable X p x q)
  have hs : CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ)
      (TopCat.of (D).regularAmbientSpace) (Set.range (D).regularComplementInclusion)ᶜ
      (P q).openNeighborhood (2 * p)
      (NormalCoclassComparison.normalCoclassCoefficient p • (D).regularThomClass) =
    (P q).normalCohomologyMap (ModuleCat.of ℚ ℚ) (2 * p)
      (NormalCoclassComparison.normalCoclassCoefficient p • CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p) := by
    rw [map_smul, map_smul, ht]
  rw [hs]
  exact FlatteningNormalCoclassComparison.centeredNormalPair_nativeCoclass_comparison p (D).regularComplementInclusion q
    (originalRegularNormalChart X p x q)
    (originalRegularNormalChart_mem_source X p x q)
    (originalRegularNormalChart_normal_center X p x q)
    (originalRegularNormalChart_range X p x q)

end

/-! # The actual homeomorphism of the unchanged regular ambient open -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (p : ℕ) (x : CycleClassMap.OriginalCycleComponent X p)

local notation "V" => OAI.AlgebraicGeometry.ComplexMultiplication.BundledAbelianBridge.originalIntegralProjectiveVariety X
local notation "D" => OAI.AlgebraicGeometry.ComplexMultiplication.Reference.DimensionCycleSupports.originalDimensionSupport X p x
local notation "OX" => OAI.AlgebraicGeometry.Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpenOver X x.val
local notation "h" => OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RegularAmbientManifold.originalRegularAmbientPointPartialHomeomorph X p x

local instance CMOriginalRegularAmbientHomeomorph.localInstance1 : TopologicalSpace (V).analyticSpace :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.analyticTopology X
local instance CMOriginalRegularAmbientHomeomorph.localInstance2 : TopologicalSpace (D).regularAnalyticSpace :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.analyticTopology (D).regularOver

/-- The actual original open inclusion identifies its point space with the native boundary complement. -/
def originalRegularAmbientHomeomorph : ComplexPoint.Basic.ComplexSchemePoint (OX) ≃ₜ (D).regularAmbientSpace :=
  let f : ComplexPoint.Basic.ComplexSchemePoint (OX) → (V).analyticSpace := (h)
  have hs : (h).source = Set.univ :=
    OpenChartRestriction.originalOpenImmersionPointPartialHomeomorph_source _
  have hf : Topology.IsOpenEmbedding f := (h).isOpenEmbedding hs
  have hr : Set.range f = ((D).regularAmbientOpen : Set (V).analyticSpace) := by
    rw [← Set.image_univ, ← hs, (h).image_source_eq_target]
    exact RegularAmbientManifold.originalRegularAmbientPointPartialHomeomorph_target X p x
  hf.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hr)

@[simp] theorem originalRegularAmbientHomeomorph_val (q : ComplexPoint.Basic.ComplexSchemePoint (OX)) :
    (originalRegularAmbientHomeomorph X p x q).val =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map
        (ComplexPoint.Basic.ComplexSchemePoint.openInclusion X (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x.val)) q := rfl

theorem originalRegularAmbientHomeomorph_symm_apply (u : (D).regularAmbientSpace) :
    (originalRegularAmbientHomeomorph X p x).symm u = (h).symm u.val := by
  have hu : u.val ∈ (h).target := by
    rw [RegularAmbientManifold.originalRegularAmbientPointPartialHomeomorph_target]
    exact u.property
  have hs : (h).source = Set.univ :=
    OpenChartRestriction.originalOpenImmersionPointPartialHomeomorph_source _
  apply ((h).isOpenEmbedding hs).injective
  have he := congrArg Subtype.val ((originalRegularAmbientHomeomorph X p x).apply_symm_apply u)
  exact he.trans ((h).right_inv hu).symm

theorem originalRegularAmbientHomeomorph_support :
    (originalRegularAmbientHomeomorph X p x) ⁻¹' Set.range (D).regularComplementInclusion =
      Set.range (ComplexPoint.Basic.Point.map (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLiftOver X x.val)) := by
  ext y
  have he := RegularFlatteningChart.originalRegularAmbientInverse_support X p x
    (originalRegularAmbientHomeomorph X p x y)
  rw [← originalRegularAmbientHomeomorph_symm_apply,
    (originalRegularAmbientHomeomorph X p x).symm_apply_apply] at he
  exact he.symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RegularAmbientHomeomorph
