import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Analytic
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.Open

/-! # Boundary -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Boundary

noncomputable section

section

/-! The omitted part of the constructed normalization divisor cover is an
actual ambient closed set of strictly higher codimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientTopology.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions
  Open.Constructions.Map Open.Constructions.Etale Open.Constructions.Regular
  Image.Constructions SchemeDivisor.Purity.Constructions Thom.Scheme.RegularSupport.Constructions ProperImage.Open.Constructions.Construction

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)

local instance : Smooth (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).hom := Normalization.AmbientMap.Constructions.smoothNormalization_smooth V W

variable (z : {x : (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).left // Order.coheight x = 1})

local instance : LocallyOfFinitePresentation (Open.Constructions.Map.sourceSupport V W z).hom :=
  inferInstanceAs (LocallyOfFinitePresentation
    (Geometric.SupportFiniteType.supportStructureMap (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z) (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).hom))

def targetGoodOpen : (Open.Constructions.Map.targetSupport V W z).left.Opens := (Open.Constructions.Regular.targetToSupport V W z).left.opensRange

theorem targetGoodOpen_genericPoint :
    genericPoint (Open.Constructions.Map.targetSupport V W z).left ∈ targetGoodOpen V W z :=
  ⟨genericPoint (Open.Constructions.Etale.targetOpen V W z).left, genericPoint_eq_of_isOpenImmersion (Open.Constructions.Regular.targetToSupport V W z).left⟩

theorem divisorMap_preimage_goodOpen :
    (Open.Constructions.Map.divisorMap V W z).left ⁻¹' (targetGoodOpen V W z : Set (Open.Constructions.Map.targetSupport V W z).left) =
      (((Open.Constructions.Map.finiteSupportMap V W z).left ⁻¹ᵁ Open.Constructions.Etale.goodOpen V W z) : Set (Open.Constructions.Map.sourceSupport V W z).left) := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    have he : (Open.Constructions.Map.imageClosureMap V W z).left ((Open.Constructions.Etale.goodOpen V W z).ι y) =
        (Open.Constructions.Map.imageClosureMap V W z).left ((Open.Constructions.Map.finiteSupportMap V W z).left x) := hy
    have he' := (Open.Constructions.Map.imageClosureMap V W z).left.isOpenEmbedding.injective he
    change (Open.Constructions.Map.finiteSupportMap V W z).left x ∈ Open.Constructions.Etale.goodOpen V W z
    exact he' ▸ y.property
  · intro hx
    exact ⟨⟨(Open.Constructions.Map.finiteSupportMap V W z).left x, hx⟩, rfl⟩

theorem divisorMap_goodOpen_smooth (x : (Open.Constructions.Map.sourceSupport V W z).left)
    (hx : (Open.Constructions.Map.divisorMap V W z).left x ∈ targetGoodOpen V W z) :
    x ∈ (Open.Constructions.Map.sourceSupport V W z).hom.smoothLocus := by
  have hp : x ∈ (Open.Constructions.Map.divisorMap V W z).left ⁻¹' (targetGoodOpen V W z : Set (Open.Constructions.Map.targetSupport V W z).left) := hx
  rw [divisorMap_preimage_goodOpen] at hp
  exact Open.Constructions.Regular.sourceOpen_subset_smoothLocus V W z hp

def omittedBoundary : Closeds V.carrier :=
  ProperImage.Open.Constructions.Construction.supportOpenBoundary (Image.Constructions.imageCycleSupport V W z) (targetGoodOpen V W z)

theorem omittedBoundary_codimension (A : IrreducibleCloseds V.carrier)
    (hA : (A : Set V.carrier) ⊆ omittedBoundary V W z) :
    Geometric.DimensionCycles.dimensionCodimension V W + 1 < Geometric.DimensionCycles.dimensionCodimension V A :=
  ProperImage.Open.Constructions.Construction.supportOpenBoundary_codimension (Image.Constructions.imageCycleSupport V W z)
    (targetGoodOpen V W z) (targetGoodOpen_genericPoint V W z) A hA

/-- Every omitted source singular point maps into the actual omitted
target boundary of the constructed finite covering. -/
theorem sourceSingularBoundary_maps_into_boundary :
    Geometric.StratumDimension.supportSingularBoundary (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z) (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).hom ⊆
      (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W).left ⁻¹' (omittedBoundary V W z : Set V.carrier) := by
  rintro x ⟨y, hy, rfl⟩
  refine ⟨(Open.Constructions.Map.divisorMap V W z).left y, ?_, ?_⟩
  · intro hmem
    exact hy (divisorMap_goodOpen_smooth V W z y hmem)
  · exact congrArg (fun f : Open.Constructions.Map.sourceSupport V W z ⟶ V.toOver => f.left y) (Open.Constructions.Map.divisorMap_ambient V W z)

end Constructions

end

/-! Retained compact ambient sets have compact normalization preimages and
avoid the actual source and target divisor singular boundaries. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Constructions.CompactSupport

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientTopology.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions
  Open.Constructions.Map Open.Constructions.Etale Open.Constructions.Regular
  Image.Constructions Constructions
  SchemeDivisor.Purity.Constructions Thom.Scheme.RegularSupport.Constructions ProperImage.Open.Constructions.Construction

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)

local instance : Smooth (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).hom := Normalization.AmbientMap.Constructions.smoothNormalization_smooth V W

theorem fullAmbientMap_compactPreimage (L : Compacts V.analyticSpace)
    (hL : (L : Set V.analyticSpace) ⊆ ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen V.toOver (Normalization.AmbientMap.Constructions.ambientOpen V W)) :
    IsCompact (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) ⁻¹' (L : Set V.analyticSpace)) := by
  let i := ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion V.toOver (Normalization.AmbientMap.Constructions.ambientOpen V W)
  have hr : (L : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) := by
    rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isImmersion i]
    change (L : Set V.analyticSpace) ⊆ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' Set.range (Normalization.AmbientMap.Constructions.ambientOpen V W).ι
    rw [Scheme.Opens.range_ι]
    exact hL
  have hc := (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion i).isEmbedding.isInducing.isCompact_preimage'
    L.isCompact hr
  have hp := (Normalization.AmbientMap.Constructions.smoothNormalization_analytic_proper V W).isCompact_preimage hc
  have he : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ∘ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.AmbientMap.Constructions.smoothNormalizationToAmbient V W) := by
    funext x
    exact ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp (Normalization.AmbientMap.Constructions.smoothNormalizationToAmbient V W) i x
  rw [he]
  exact hp

variable (z : {x : (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).left // Order.coheight x = 1})

local instance : LocallyOfFinitePresentation (Open.Constructions.Map.targetSupport V W z).hom :=
  inferInstanceAs (LocallyOfFinitePresentation
    (Geometric.SupportFiniteType.supportStructureMap (Image.Constructions.imageSupport V W z) V.structureMap))

theorem targetGoodOpen_smooth :
    targetGoodOpen V W z ≤ (Open.Constructions.Map.targetSupport V W z).hom.smoothLocus := by
  have hw : (Open.Constructions.Regular.targetToSupport V W z).left ≫ (Open.Constructions.Map.targetSupport V W z).hom = (Open.Constructions.Etale.targetOpen V W z).hom :=
    (Open.Constructions.Regular.targetToSupport V W z).w
  let : Smooth ((Open.Constructions.Regular.targetToSupport V W z).left ≫ (Open.Constructions.Map.targetSupport V W z).hom) := by rw [hw]; infer_instance
  exact Product.SupportTo.Constructions.SmoothOpen.openImmersion_range_subset_smoothLocus
    (Open.Constructions.Regular.targetToSupport V W z).left (Open.Constructions.Map.targetSupport V W z).hom

theorem boundaryComplement_subset_targetRegular :
    (ProperImage.CompactProjection.Constructions.Construction.algebraicComplementOpen V (omittedBoundary V W z) : Set V.analyticSpace) ⊆
      (Image.Constructions.imageCycleSupport V W z).regularAmbientOpen :=
  ProperImage.Open.Constructions.Construction.boundaryComplement_subset_regularAmbient (Image.Constructions.imageCycleSupport V W z) (targetGoodOpen V W z)
    (targetGoodOpen_smooth V W z)

theorem boundaryComplement_preimage_subset_sourceRegular :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) ⁻¹'
      (ProperImage.CompactProjection.Constructions.Construction.algebraicComplementOpen V (omittedBoundary V W z) : Set V.analyticSpace) ⊆
    Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z) := by
  intro x hx hs
  exact hx (sourceSingularBoundary_maps_into_boundary V W z hs)

end Constructions.CompactSupport

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Boundary
