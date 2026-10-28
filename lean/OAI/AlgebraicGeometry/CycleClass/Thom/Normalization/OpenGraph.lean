import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GenericFibers
import OAI.AlgebraicGeometry.CycleClass.Thom.GenericGraph
import OAI.AlgebraicGeometry.CycleClass.Thom.RestrictedGraphSmallerFibers

/-! # Open Graph -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenGraph.Constructions.Class

noncomputable section

/-! A bounded coordinate graph of an actual open subscheme of the smooth normalization projects to the original supported cycle class, including across the singular part of its image. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GenericCover.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Open.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GenericFibers.Constructions.Open OAI.AlgebraicGeometry.CycleClass.Thom.GenericGraph.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.RestrictedGraphSmallerFibers.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.GoodOpenMap.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GraphBaseRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularNeighborhoodDetection.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)

local instance : IsIntegral D.toOver.left := inferInstanceAs (IsIntegral D.scheme)
local instance : LocallyOfFiniteType D.toOver.hom := inferInstanceAs (LocallyOfFiniteType D.structureMap)

variable {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  (a : X ⟶ AmbientMap.Constructions.smoothNormalizationOver V D.val) [IsOpenImmersion a.left]
  (U : Opens V.analyticSpace)
  (hcover : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (PrincipalBoundary.Constructions.fullAmbientMap V D.val) ⁻¹' (U : Set V.analyticSpace) ⊆
    Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a))

local notation "MX" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ

variable {d : ℕ} (e : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X → Fin d → ℂ)

variable (he : ContMDiff 𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ))
  𝓘(ℂ, Fin d → ℂ) ω e)

local instance (A : Opens V.analyticSpace) : MetrizableSpace A := A.isOpenEmbedding'.isEmbedding.metrizableSpace
local instance (priority := low) (A : Opens V.analyticSpace) :
    ChartedSpace (V.analyticModel × (Fin d → ℂ)) (A × (Fin d → ℂ)) :=
  prodChartedSpace V.analyticModel A (Fin d → ℂ) (Fin d → ℂ)
local instance (A : Opens V.analyticSpace) : IsManifold 𝓘(ℂ, V.analyticModel × (Fin d → ℂ)) ω (A × (Fin d → ℂ)) :=
  Product.Immersion.Constructions.productModel_isManifold

abbrev normalizationOpenGraph : GraphOpenImmersion.Constructions.graphSourceOpen (GenericFibers.Constructions.Open.openBase D a) (GenericFibers.Constructions.Open.openBase_analytic D a) U → U × (Fin d → ℂ) :=
  RestrictedGraphSmallerFibers.Constructions.firstGraph (GenericFibers.Constructions.Open.openBase D a) (GenericFibers.Constructions.Open.openBase_analytic D a) e U

include he in
omit [IsOpenImmersion a.left] in
theorem normalizationOpenGraph_analytic :
    ContMDiff 𝓘(ℂ, MX) 𝓘(ℂ, V.analyticModel × (Fin d → ℂ)) ω (normalizationOpenGraph D a U e) :=
  GraphOpenImmersion.Constructions.restrictedGraph_analytic (GenericFibers.Constructions.Open.openBase D a) (GenericFibers.Constructions.Open.openBase_analytic D a) U e he

abbrev retainedNormalizationSource := GenericGraph.Constructions.Class.retainedSource D (GenericCover.Constructions.goodOpen D.toOver) U
  (normalizationOpenGraph D a U e) (normalizationOpenGraph_analytic D a U e he)

theorem normalizationOpenGraph_generic_differential_injective
    (x : retainedNormalizationSource D a U e he) :
    Function.Injective (mfderiv 𝓘(ℂ, MX) 𝓘(ℂ, V.analyticModel)
      (Prod.fst ∘ GenericGraph.Constructions.Class.retainedGraph D (GenericCover.Constructions.goodOpen D.toOver) U (normalizationOpenGraph D a U e)
        (normalizationOpenGraph_analytic D a U e he)) x) := by
  have hd := RestrictedGraphSmallerFibers.Constructions.doubleGraph_projected_mfderiv (GenericFibers.Constructions.Open.openBase D a) (GenericFibers.Constructions.Open.openBase_analytic D a) e he U
    (Cycle.GoodOpenMap.Constructions.goodNeighborhood D (GenericCover.Constructions.goodOpen D.toOver) U) inf_le_left x
  exact (congrArg (fun L : MX →L[ℂ] V.analyticModel => Function.Injective L) hd).mpr
    (GenericFibers.Constructions.Open.openBase_good_differential_injective D a x.val.val x.property.2)

include hcover in
theorem normalizationOpenGraph_genericFiber_card
    (x : GraphOpenImmersion.Constructions.graphSourceOpen D.regularComplementInclusion (D.contMDiff_regularComplementInclusion ω)
      (Cycle.RegularNeighborhoodDetection.Constructions.regularNeighborhood D (Cycle.GoodOpenMap.Constructions.goodNeighborhood D (GenericCover.Constructions.goodOpen D.toOver) U))) :
    Nat.card {y : retainedNormalizationSource D a U e he |
      (GenericGraph.Constructions.Class.retainedGraph D (GenericCover.Constructions.goodOpen D.toOver) U (normalizationOpenGraph D a U e)
        (normalizationOpenGraph_analytic D a U e he) y).1 =
          Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion D (Cycle.GoodOpenMap.Constructions.goodNeighborhood D (GenericCover.Constructions.goodOpen D.toOver) U)
            (GenericGraph.Constructions.Class.retainedRegular D (GenericCover.Constructions.goodOpen D.toOver) (GenericCover.Constructions.goodOpen_subset_smoothLocus D.toOver) U) x} = 1 := by
  let P := Cycle.GoodOpenMap.Constructions.goodNeighborhood D (GenericCover.Constructions.goodOpen D.toOver) U
  let u : P := Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion D P
    (GenericGraph.Constructions.Class.retainedRegular D (GenericCover.Constructions.goodOpen D.toOver) (GenericCover.Constructions.goodOpen_subset_smoothLocus D.toOver) U) x
  have hu : u.val ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Open.Constructions.targetToAmbient D)) := by
    have hr : u ∈ Set.range (Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion D P
        (GenericGraph.Constructions.Class.retainedRegular D (GenericCover.Constructions.goodOpen D.toOver) (GenericCover.Constructions.goodOpen_subset_smoothLocus D.toOver) U)) := ⟨x, rfl⟩
    rw [← Open.Constructions.targetToAmbient_range D P (fun _ hx => hx.2)] at hr
    exact hr
  have hd := RestrictedGraphSmallerFibers.Constructions.doubleGraph_fiber_card (GenericFibers.Constructions.Open.openBase D a) (GenericFibers.Constructions.Open.openBase_analytic D a) e he U P inf_le_left u
  exact hd.trans (GenericFibers.Constructions.Open.openBase_genericFiber_card D a U hcover ⟨u.val, u.property.1⟩ hu)

omit [IsOpenImmersion a.left] in
theorem normalizationOpenGraph_bound (K : Set (Fin d → ℂ))
    (hb : ∀ x, GenericFibers.Constructions.Open.openBase D a x ∈ U → e x ∈ K) :
    Set.range (normalizationOpenGraph D a U e) ⊆
      ((Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion) ×ˢ K := by
  rintro _ ⟨x, rfl⟩
  exact ⟨GenericFibers.Constructions.Open.openBase_mem_support D a x.val, hb x.val x.property⟩

include hcover in
theorem normalizationOpenGraph_project_cycleClass
    (hei : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, MX) 𝓘(ℂ, Fin d → ℂ) e x))
    (hc : Topology.IsClosedEmbedding (normalizationOpenGraph D a U e))
    (K : Set (Fin d → ℂ)) (hK : IsCompact K) (hb : ∀ x, GenericFibers.Constructions.Open.openBase D a x ∈ U → e x ∈ K) :
    Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of U) ((Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion)
      K hK (Set.range (normalizationOpenGraph D a U e)) (normalizationOpenGraph_bound D a U e K hb)
      (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm
      (Degree.Constructions.ThomClass.complexThomClassInDegree (normalizationOpenGraph D a U e) (normalizationOpenGraph_analytic D a U e he)
        (GraphOpenImmersion.Constructions.restrictedGraph_differential_injective (GenericFibers.Constructions.Open.openBase D a) (GenericFibers.Constructions.Open.openBase_analytic D a) U e he hei)
        hc (p + d) (GenericFibers.Constructions.Open.openGraph_codimension D a d)) =
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
        (Set.range D.analyticInclusion)ᶜ U (2 * p) D.rationalSupportedCycleClass := by
  have hdeg := normalizationOpenGraph_genericFiber_card D a U hcover e he
  have hfin := fun x => Nat.finite_of_card_ne_zero (show Nat.card _ ≠ 0 from (hdeg x).trans_ne (by decide))
  have h := GenericGraph.Constructions.Class.graphThom_project_genericCycleClass D (GenericCover.Constructions.goodOpen D.toOver) (GenericCover.Constructions.goodOpen_subset_smoothLocus D.toOver) U
    (normalizationOpenGraph D a U e) (normalizationOpenGraph_analytic D a U e he) (GenericCover.Constructions.goodOpen_spec D.toOver).1
    (GraphOpenImmersion.Constructions.restrictedGraph_differential_injective (GenericFibers.Constructions.Open.openBase D a) (GenericFibers.Constructions.Open.openBase_analytic D a) U e he hei)
    hc (GenericFibers.Constructions.Open.openGraph_codimension D a d) K hK (normalizationOpenGraph_bound D a U e K hb)
    (normalizationOpenGraph_generic_differential_injective D a U e he) hfin 1 hdeg
  simpa only [Nat.cast_one, one_smul] using h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenGraph.Constructions.Class
