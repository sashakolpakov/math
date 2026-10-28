import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Boundary
import OAI.AlgebraicGeometry.CycleClass.Thom.SmoothSupportOpenRange

/-! # Range -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Range

/-! Every retained regular support point lies in the actual smooth opens
of the constructed normalization covering. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Constructions.RegularRange

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientTopology.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions
  Open.Constructions.Map Open.Constructions.Etale Open.Constructions.Regular
  Image.Constructions Boundary.Constructions SchemeDivisor.Purity.Constructions
  Thom.Scheme.RegularSupport.Constructions

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)

local instance : Smooth (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).hom := Normalization.AmbientMap.Constructions.smoothNormalization_smooth V W
local instance : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W)) :=
  Normalization.AmbientTopology.Constructions.smoothNormalization_metrizable V W
local instance : LocallyOfFiniteType V.toOver.hom := inferInstanceAs (LocallyOfFiniteType V.structureMap)

variable (z : {x : (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).left // Order.coheight x = 1})

theorem supportPoint_mem_goodPreimage (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Open.Constructions.Map.sourceSupport V W z))
    (hy : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W)
      (Thom.Scheme.RegularSupport.Constructions.supportInclusion (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z) y) ∈
        ProperImage.CompactProjection.Constructions.Construction.algebraicComplementOpen V (Boundary.Constructions.omittedBoundary V W z)) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying y ∈ (Open.Constructions.Map.finiteSupportMap V W z).left ⁻¹ᵁ Open.Constructions.Etale.goodOpen V W z := by
  have he : (Image.Constructions.imageCycleSupport V W z).analyticInclusion (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Open.Constructions.Map.divisorMap V W z) y) =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W)
        (Thom.Scheme.RegularSupport.Constructions.supportInclusion (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z) y) := by
    change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Thom.Scheme.RegularSupport.Constructions.supportToAmbient V.toOver (Image.Constructions.imageSupport V W z))
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Open.Constructions.Map.divisorMap V W z) y) = _
    have h := congrArg (fun f : Open.Constructions.Map.sourceSupport V W z ⟶ V.toOver => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f y)
      (Open.Constructions.Map.divisorMap_ambient V W z)
    simpa only [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp] using h
  have hm := ProperImage.Open.Constructions.Construction.supportPoint_mem_open_of_boundaryComplement (Image.Constructions.imageCycleSupport V W z) (Boundary.Constructions.targetGoodOpen V W z)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Open.Constructions.Map.divisorMap V W z) y) (by rw [he]; exact hy)
  have hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying y ∈ (Open.Constructions.Map.divisorMap V W z).left ⁻¹'
      (Boundary.Constructions.targetGoodOpen V W z : Set (Open.Constructions.Map.targetSupport V W z).left) := hm
  rw [Boundary.Constructions.divisorMap_preimage_goodOpen] at hx
  exact hx

theorem sourceRegularPreimage_subset_cover_range (L : Set V.analyticSpace)
    (hL : L ⊆ ProperImage.CompactProjection.Constructions.Construction.algebraicComplementOpen V (Boundary.Constructions.omittedBoundary V W z)) :
    PrimeDivisorCompactTrace.Constructions.regularAmbientMap (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z ⁻¹'
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) ⁻¹' L) ⊆
    Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Open.Constructions.Regular.sourceToRegular V W z)) := by
  have hr := Thom.Scheme.SmoothSupportOpen.Constructions.smoothOpenToRegular_range (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W)
    (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z) _ (Open.Constructions.Regular.sourceOpen_subset_smoothLocus V W z)
  change Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Open.Constructions.Regular.sourceToRegular V W z)) = _ at hr
  rw [hr]
  intro x hx
  apply supportPoint_mem_goodPreimage V W z
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Thom.Scheme.SmoothSupportOpen.Constructions.regularToSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W)
      (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z)) x)
  have he : Thom.Scheme.RegularSupport.Constructions.supportInclusion (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Thom.Scheme.SmoothSupportOpen.Constructions.regularToSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W)
        (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z)) x) =
    PrimeDivisorCompactTrace.Constructions.regularAmbientMap (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z x := by
    exact (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp
      (Thom.Scheme.SmoothSupportOpen.Constructions.regularToSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W)
        (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z))
      (Thom.Scheme.RegularSupport.Constructions.supportToAmbient (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z)) x).symm
  rw [he]
  exact hL hx

theorem targetRegularPreimage_subset_cover_range (L : Set V.analyticSpace)
    (hL : L ⊆ ProperImage.CompactProjection.Constructions.Construction.algebraicComplementOpen V (Boundary.Constructions.omittedBoundary V W z)) :
    ProperImage.Projection.Constructions.Construction.regularAmbientMap (Image.Constructions.imageCycleSupport V W z) ⁻¹' L ⊆
      Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Open.Constructions.Regular.targetToRegular V W z)) := by
  have hr := SmoothSupportOpenRange.Constructions.smoothOpenToRegular_range (Y := V.toOver)
    (Image.Constructions.imageSupport V W z) (Open.Constructions.Regular.targetToSupport V W z)
  change Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Open.Constructions.Regular.targetToRegular V W z)) = _ at hr
  rw [hr]
  intro x hx
  rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isImmersion (Open.Constructions.Regular.targetToSupport V W z)]
  exact ProperImage.Open.Constructions.Construction.supportPoint_mem_open_of_boundaryComplement (Image.Constructions.imageCycleSupport V W z) (Boundary.Constructions.targetGoodOpen V W z)
    ((Image.Constructions.imageCycleSupport V W z).regularAnalyticInclusion x) (hL hx)

end Constructions.RegularRange

end AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Range

namespace AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Range.Constructions.BranchRange

/-! Over the actual retained ambient open, the normalization divisor cover contains every point of the full source divisor support, including all branches. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientTopology.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Open.Constructions.Map OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Open.Constructions.Etale OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Open.Constructions.Regular
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Analytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Boundary.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Range.Constructions.RegularRange
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)

local instance : Smooth (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).hom := Normalization.AmbientMap.Constructions.smoothNormalization_smooth V W

variable (z : {x : (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).left // Order.coheight x = 1})

theorem sourceAmbientMap_point (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Open.Constructions.Etale.sourceOpen V W z)) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Analytic.Constructions.sourceAmbientMap V W z) x =
      Thom.Scheme.RegularSupport.Constructions.supportInclusion (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z)
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion (Open.Constructions.Map.sourceSupport V W z)
          ((Open.Constructions.Map.finiteSupportMap V W z).left ⁻¹ᵁ Open.Constructions.Etale.goodOpen V W z)) x) := by
  have h := congrArg (fun f => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x) (Open.Constructions.Regular.sourceToRegular_ambient V W z)
  exact h.trans (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp
    (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion (Open.Constructions.Map.sourceSupport V W z) ((Open.Constructions.Map.finiteSupportMap V W z).left ⁻¹ᵁ Open.Constructions.Etale.goodOpen V W z))
    (Thom.Scheme.RegularSupport.Constructions.supportToAmbient (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z)) x)

theorem sourceAmbientMap_range_subset_prime : Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Analytic.Constructions.sourceAmbientMap V W z)) ⊆
    Set.range (Thom.Scheme.RegularSupport.Constructions.supportInclusion (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z)) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion (Open.Constructions.Map.sourceSupport V W z)
    ((Open.Constructions.Map.finiteSupportMap V W z).left ⁻¹ᵁ Open.Constructions.Etale.goodOpen V W z)) x, (sourceAmbientMap_point V W z x).symm⟩

theorem fullPrime_point_mem_cover_range (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W))
    (hy : y ∈ Set.range (Thom.Scheme.RegularSupport.Constructions.supportInclusion (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z)))
    (hU : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) y ∈ ProperImage.CompactProjection.Constructions.Construction.algebraicComplementOpen V (Boundary.Constructions.omittedBoundary V W z)) :
    y ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Analytic.Constructions.sourceAmbientMap V W z)) := by
  obtain ⟨t, rfl⟩ := hy
  have ht := RegularRange.supportPoint_mem_goodPreimage V W z t hU
  let i := ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion (Open.Constructions.Map.sourceSupport V W z) ((Open.Constructions.Map.finiteSupportMap V W z).left ⁻¹ᵁ Open.Constructions.Etale.goodOpen V W z)
  have hr : t ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) := by
    rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isImmersion i]
    change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying t ∈ Set.range (((Open.Constructions.Map.finiteSupportMap V W z).left ⁻¹ᵁ Open.Constructions.Etale.goodOpen V W z).ι)
    rw [Scheme.Opens.range_ι]
    exact ht
  obtain ⟨x, hx⟩ := hr
  refine ⟨x, ?_⟩
  exact (sourceAmbientMap_point V W z x).trans
    (congrArg (Thom.Scheme.RegularSupport.Constructions.supportInclusion (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z)) hx)

end AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Range.Constructions.BranchRange

end

end OAI
