import OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.LocalSerreCancellation
import OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.SourceNeighborhood
import OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.IntersectionSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.ClosedIntersectionRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectiveSupportIsolation

/-! # Positive Serre Intersection -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.PositiveSerreIntersection.Constructions.ComponentComparison

/-! The actual supported cup and the original Serre intersection cycle
agree near every minimum-codimension component in positive dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.LocalIsolation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.LocalSerreCancellation.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.SourceNeighborhood.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.SupportedProduct.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.AnalyticImage.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.IntersectionSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.ClosedIntersectionRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenProduct.Constructions.Class
open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ImmersionOpenRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectiveSupportIsolation.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SupportDetection.Constructions.Neighborhoods OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.MinimalSupport.Constructions.Isolation OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SupportLocalDetection.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectiveSupportIsolation.Constructions.Intersection OAI.AlgebraicGeometry.CycleClass.Thom.Closed.Intersection.Constructions.Class
open OAI.AlgebraicGeometry.CycleClass.Thom.EtaleProjectiveNeighborhood.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ)
  (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport V q)

local instance : IsIntegral V.toOver.left := V.property
local instance : Smooth V.toOver.hom := V.presentation.smooth
local instance : AlgebraicGeometry.IsNoetherian V.toOver.left := inferInstanceAs (AlgebraicGeometry.IsNoetherian V.carrier)
local instance : IsIntegral (Diagonal.Ambient.Constructions.productVariety V V).toOver.left := (Diagonal.Ambient.Constructions.productVariety V V).property
local instance : Smooth (Diagonal.Ambient.Constructions.productVariety V V).toOver.hom := (Diagonal.Ambient.Constructions.productVariety V V).presentation.smooth

variable (hproper : ∀ Z : IrreducibleCloseds V.carrier,
  (Z : Set V.carrier) ⊆ Supported.ProjectiveSupportIsolation.Constructions.Intersection.intersectionClosed V p q A B → p + q ≤ Geometric.DimensionCycles.dimensionCodimension V Z)

local notation "F" => OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectiveSupportIsolation.Constructions.Intersection.intersectionClosed V p q A B

theorem exists_component_comparison (hpos : 0 < V.complexDimension) (M : Scheme.SupportDetection.Constructions.Neighborhoods.MinimalSupport V.toOver F (p + q)) :
    ∃ K : V.carrier.Opens, IntersectionGeometry.supportPoint M.val ∈ K ∧
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
        (V.analyticUnderlying ⁻¹' (F : Set V.carrier))ᶜ (Scheme.SectionEvaluation.Constructions.analyticOpen V.toOver K) (2 * (p + q))
        (Closed.Intersection.Constructions.Class.closedIntersectionClass V p q A B) =
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
        (V.analyticUnderlying ⁻¹' (F : Set V.carrier))ᶜ (Scheme.SectionEvaluation.Constructions.analyticOpen V.toOver K) (2 * (p + q))
        (Supported.Map.Constructions.relativeClassMap V F (p + q) (Supported.ProjectiveSupportIsolation.Constructions.Intersection.supportedPairCycle V p q A B hproper)) := by
  let Z := Supported.ProjectiveSupportIsolation.Constructions.minimalCycleSupport V F (p + q) M
  have hxF : IntersectionGeometry.supportPoint Z.val ∈ F := M.property.1 (Z.val.isIrreducible.isGenericPoint_genericPoint Z.val.isClosed).mem
  have hxA : IntersectionGeometry.supportPoint Z.val ∈ (A.val : Set V.carrier) := hxF.1
  have hxB : IntersectionGeometry.supportPoint Z.val ∈ (B.val : Set V.carrier) := hxF.2
  obtain ⟨X, hX, j, hj, hI, hS, ⟨y, hy⟩, ac, ht, he⟩ := EtaleProjectiveNeighborhood.Constructions.exists_etale_projective_neighborhood V Z.genericPoint
  let := hX
  let := hj
  let := hI
  let := hS
  let := ac
  let := ht
  let := he
  obtain ⟨W, hWB, hzW, hf⟩ := Diagonal.LocalSerreCancellation.Constructions.exists_chart_serre_pullback_formula V p q A B Z X j hpos hxA hxB hproper y hy
  let J := Scheme.MinimalSupport.Constructions.Isolation.isolatingOpen V.toOver F (p + q) M
  let K : V.carrier.Opens := ((Diagonal.Ambient.Constructions.diagonal V).left ⁻¹ᵁ W) ⊓ J
  have hc := Supported.ProjectiveSupportIsolation.Constructions.support_dimension_bound V F (p + q) hproper
  refine ⟨K, ⟨?_, Scheme.MinimalSupport.Constructions.Isolation.genericPoint_mem_isolatingOpen V.toOver F (p + q) M hc⟩, ?_⟩
  · change (Diagonal.Ambient.Constructions.diagonal V).left Z.genericPoint ∈ W
    rw [← Diagonal.Ambient.Constructions.diagonalSupport_genericPoint V (p + q) Z]
    exact hzW
  · apply Scheme.SupportLocalDetection.Constructions.relativeClass_eq_on_open_of_local V.toOver F (p + q) hc (Scheme.SectionEvaluation.Constructions.analyticOpen V.toOver K)
    intro x hxK _hxF
    have hxR : x ∈ Z.regularAmbientOpen := hxK.2.2
    have hxW : Diagonal.SupportedProduct.Constructions.diagonalPointMap V x ∈ Scheme.SectionEvaluation.Constructions.analyticOpen (Diagonal.Ambient.Constructions.productVariety V V).toOver W := by
      change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Diagonal.Ambient.Constructions.diagonal V) x) ∈ W
      rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying_map]
      exact hxK.1
    let G := Scheme.SectionEvaluation.Constructions.analyticOpen (Diagonal.Ambient.Constructions.productVariety V V).toOver W ⊓ (Diagonal.Ambient.Constructions.diagonalSupport V (p + q) Z).regularAmbientOpen
    have hGB : (G : Set (Diagonal.Ambient.Constructions.productVariety V V).analyticSpace) ⊆
        Scheme.SectionEvaluation.Constructions.analyticOpen (Diagonal.Ambient.Constructions.productVariety V V).toOver (Diagonal.OpenEquations.Constructions.productOpen V X j) :=
      fun _ hg => hWB hg.1
    have hxG : Diagonal.SupportedProduct.Constructions.diagonalPointMap V x ∈ G :=
      ⟨hxW, (Diagonal.IntersectionSupport.Constructions.diagonalCycle_regular_iff V p q Z x).mpr hxR⟩
    obtain ⟨U, hUG, hxU, hUK, hUP, hUB, O, hi, hO⟩ := Diagonal.SourceNeighborhood.Constructions.exists_diagonal_source_neighborhood V X j V.complexDimension
      G hGB (Scheme.SectionEvaluation.Constructions.analyticOpen V.toOver K) x hxG hxK
    have hUW : (U : Set (Diagonal.Ambient.Constructions.productVariety V V).analyticSpace) ⊆ Scheme.SectionEvaluation.Constructions.analyticOpen (Diagonal.Ambient.Constructions.productVariety V V).toOver W :=
      fun _ hu => (hUG hu).1
    have hUR : (U : Set (Diagonal.Ambient.Constructions.productVariety V V).analyticSpace) ⊆ (Diagonal.Ambient.Constructions.diagonalSupport V (p + q) Z).regularAmbientOpen :=
      fun _ hu => (hUG hu).2
    have hl := hf U hUW hUP hUB hUR O hi hO (Diagonal.OpenProduct.Constructions.Class.pairedOpenInclusion V p q A B U)
      (Diagonal.OpenProduct.Constructions.Class.pairedOpenInclusion_closed V p q A B U) (Diagonal.OpenProduct.Constructions.Class.pairedCycle_supported V p q A B U)
      (Diagonal.IntersectionSupport.Constructions.diagonalCycle_pairedOpen_supported V p q A B Z hxA hxB U)
    rw [Diagonal.OpenProduct.Constructions.Class.diagonalOpen_productClass V p q A B U] at hl
    have ho : ∀ T : Supported.Map.Constructions.SupportedSupport V F (p + q),
        T ≠ Supported.ProjectiveSupportIsolation.Constructions.minimalSupportedSupport V F (p + q) M →
        ∀ t : Closed.ImmersionOpenRestriction.Constructions.sourceOpen (Diagonal.ComplexImmersion.Constructions.diagonalImmersion V) U, t.val ∉ Set.range T.val.analyticInclusion := by
      intro T hT t ht
      rw [T.val.range_analyticInclusion] at ht
      exact Supported.ProjectiveSupportIsolation.Constructions.isolatingOpen_avoids_other V F (p + q) hproper M T hT (hUK t.property).2 ht
    exact ⟨Closed.ImmersionOpenRestriction.Constructions.sourceOpen (Diagonal.ComplexImmersion.Constructions.diagonalImmersion V) U, hxU,
      (Diagonal.ClosedIntersectionRestriction.Constructions.closedIntersection_restriction_iff V p q A B U (Supported.ProjectiveSupportIsolation.Constructions.minimalSupportedSupport V F (p + q) M) hproper ho).mpr hl⟩

end AlgebraicGeometry.CycleClass.Thom.PositiveSerreIntersection.Constructions.ComponentComparison

namespace AlgebraicGeometry.CycleClass.Thom.PositiveSerreIntersection.Constructions

/-! In positive dimension, the actual geometric cycle class takes
the original proper Serre intersection cycle to the original cup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.PositiveSerreIntersection.Constructions.ComponentComparison OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectiveSupportIsolation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SupportDetection.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectiveSupportIsolation.Constructions.Intersection OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Map.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Closed.Intersection.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ)
  (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport V q)
  (hproper : ∀ Z : IrreducibleCloseds V.carrier,
    (Z : Set V.carrier) ⊆ Supported.ProjectiveSupportIsolation.Constructions.Intersection.intersectionClosed V p q A B → p + q ≤ Geometric.DimensionCycles.dimensionCodimension V Z)

local instance : IsIntegral V.toOver.left := V.property
local instance : Smooth V.toOver.hom := V.presentation.smooth
local instance : AlgebraicGeometry.IsNoetherian V.toOver.left := inferInstanceAs (AlgebraicGeometry.IsNoetherian V.carrier)

theorem closedIntersection_eq_serre (hpos : 0 < V.complexDimension) :
    Closed.Intersection.Constructions.Class.closedIntersectionClass V p q A B =
      Supported.Map.Constructions.relativeClassMap V (Supported.ProjectiveSupportIsolation.Constructions.Intersection.intersectionClosed V p q A B) (p + q) (Supported.ProjectiveSupportIsolation.Constructions.Intersection.supportedPairCycle V p q A B hproper) := by
  choose K hK hEq using ComponentComparison.exists_component_comparison V p q A B hproper hpos
  exact Scheme.SupportDetection.Constructions.relativeClass_eq_of_component_neighborhoods V.toOver (Supported.ProjectiveSupportIsolation.Constructions.Intersection.intersectionClosed V p q A B) (p + q)
    (Supported.ProjectiveSupportIsolation.Constructions.support_dimension_bound V (Supported.ProjectiveSupportIsolation.Constructions.Intersection.intersectionClosed V p q A B) (p + q) hproper) K hK _ _ hEq

theorem geometricClass_supportedSerreCycle (hpos : 0 < V.complexDimension) :
    V.geometricCycleClassMap (p + q)
      (Supported.Map.Constructions.forgetCycle V (Supported.ProjectiveSupportIsolation.Constructions.Intersection.intersectionClosed V p q A B) (p + q) (Supported.ProjectiveSupportIsolation.Constructions.Intersection.supportedPairCycle V p q A B hproper)) =
    cast (congrArg (fun n => (V.rationalCohomology n : Type)) (add_add_add_comm p p q q))
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (Betti.Scheme.schemePointSpace V.toOver) (p + p) (q + q)
        A.geometricCycleClass B.geometricCycleClass) := by
  have h := congrArg (fun c => cast (congrArg (fun n => (V.rationalCohomology n : Type)) (two_mul (p + q)))
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
      (V.analyticUnderlying ⁻¹' (Supported.ProjectiveSupportIsolation.Constructions.Intersection.intersectionClosed V p q A B : Set V.carrier))ᶜ (2 * (p + q)) c))
    (closedIntersection_eq_serre V p q A B hproper hpos).symm
  exact (Supported.Map.Constructions.relativeClassMap_forget V (Supported.ProjectiveSupportIsolation.Constructions.Intersection.intersectionClosed V p q A B) (p + q)
    (Supported.ProjectiveSupportIsolation.Constructions.Intersection.supportedPairCycle V p q A B hproper)).symm.trans
      (h.trans (Closed.Intersection.Constructions.Class.closedIntersectionClass_geometricCup V p q A B))

end AlgebraicGeometry.CycleClass.Thom.PositiveSerreIntersection.Constructions

end

end OAI
