import OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.OpenProjectionSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.GoodOpenMap
import OAI.AlgebraicGeometry.CycleClass.Thom.Product.SmallerOpenProjection
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.Open

/-! # Generic Graph -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.GenericGraph.Constructions.Class

noncomputable section

/-! A bounded closed holomorphic graph over an arbitrary cycle projects to its generic fiber degree times the original supported cycle class. Finiteness and unramifiedness are needed only on a dense smooth support open; actual purity extends the equality across its omitted boundary. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.GoodOpenMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.Open.Constructions.Construction OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularNeighborhoodDetection.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Product.SmallerOpen.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Product.SmallerOpenProjection.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.SubsetHomeomorph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.ProductHomeomorphAnalytic.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.OpenProjectionSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (W : D.scheme.Opens) (hWs : W ≤ D.structureMap.smoothLocus) (U : Opens V.analyticSpace)

include hWs in
theorem retainedRegular : (Cycle.GoodOpenMap.Constructions.goodNeighborhood D W U : Set V.analyticSpace) ⊆ D.regularAmbientOpen :=
  (show (Cycle.GoodOpenMap.Constructions.goodNeighborhood D W U : Set V.analyticSpace) ⊆
    ProperImage.CompactProjection.Constructions.Construction.algebraicComplementOpen V (ProperImage.Open.Constructions.Construction.supportOpenBoundary D W) from fun _ hx => hx.2).trans
      (ProperImage.Open.Constructions.Construction.boundaryComplement_subset_regularAmbient D W hWs)

variable {L E : Type} [TopologicalSpace L] [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedSpace ℝ E] [ChartedSpace E L] [IsManifold 𝓘(ℂ, E) ω L] {d : ℕ}

local instance (A : Opens V.analyticSpace) : MetrizableSpace A := A.isOpenEmbedding'.isEmbedding.metrizableSpace
local instance (priority := low) (A : Opens V.analyticSpace) :
    ChartedSpace (V.analyticModel × (Fin d → ℂ)) (A × (Fin d → ℂ)) :=
  prodChartedSpace V.analyticModel A (Fin d → ℂ) (Fin d → ℂ)
local instance (A : Opens V.analyticSpace) : IsManifold 𝓘(ℂ, V.analyticModel × (Fin d → ℂ)) ω (A × (Fin d → ℂ)) :=
  Product.Immersion.Constructions.productModel_isManifold

variable (i : L → U × (Fin d → ℂ)) (hi : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, V.analyticModel × (Fin d → ℂ)) ω i)

abbrev retainedSource := GraphOpenImmersion.Constructions.graphSourceOpen i hi (Open.ProductHomeomorphAnalytic.Constructions.productBaseOpen (Open.SubsetHomeomorph.Constructions.insideOpen U (Cycle.GoodOpenMap.Constructions.goodNeighborhood D W U)))

def retainedGraph : retainedSource D W U i hi → Cycle.GoodOpenMap.Constructions.goodNeighborhood D W U × (Fin d → ℂ) :=
  Product.SmallerOpen.Constructions.smallerGraph U (Cycle.GoodOpenMap.Constructions.goodNeighborhood D W U) inf_le_left i hi

theorem graphThom_project_genericCycleClass (hW : genericPoint D.scheme ∈ W)
    (hii : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, V.analyticModel × (Fin d → ℂ)) i x))
    (hc : Topology.IsClosedEmbedding i) (hp : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E (V.analyticModel × (Fin d → ℂ)) = p + d)
    (K : Set (Fin d → ℂ)) (hK : IsCompact K)
    (hT : Set.range i ⊆ ((Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion) ×ˢ K)
    (hip : ∀ x : retainedSource D W U i hi,
      Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, V.analyticModel) (Prod.fst ∘ retainedGraph D W U i hi) x))
    (hfin : ∀ x : GraphOpenImmersion.Constructions.graphSourceOpen D.regularComplementInclusion (D.contMDiff_regularComplementInclusion ω)
      (Cycle.RegularNeighborhoodDetection.Constructions.regularNeighborhood D (Cycle.GoodOpenMap.Constructions.goodNeighborhood D W U)),
      Finite {y : retainedSource D W U i hi | (retainedGraph D W U i hi y).1 =
        Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion D (Cycle.GoodOpenMap.Constructions.goodNeighborhood D W U) (retainedRegular D W hWs U) x})
    (m : ℕ) (hdeg : ∀ x : GraphOpenImmersion.Constructions.graphSourceOpen D.regularComplementInclusion (D.contMDiff_regularComplementInclusion ω)
      (Cycle.RegularNeighborhoodDetection.Constructions.regularNeighborhood D (Cycle.GoodOpenMap.Constructions.goodNeighborhood D W U)),
      Nat.card {y : retainedSource D W U i hi | (retainedGraph D W U i hi y).1 =
        Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion D (Cycle.GoodOpenMap.Constructions.goodNeighborhood D W U) (retainedRegular D W hWs U) x} = m) :
    Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of U) ((Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion)
      K hK (Set.range i) hT (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm
      (Degree.Constructions.ThomClass.complexThomClassInDegree i hi hii hc (p + d) hp) =
      (m : ℚ) • Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
        (Set.range D.analyticInclusion)ᶜ U (2 * p) D.rationalSupportedCycleClass := by
  apply Cycle.GoodOpenMap.Constructions.goodOpenPullback_injective D W U hW
  rw [map_smul, Cycle.GoodOpenMap.Constructions.goodOpenPullback_cycleClass]
  have hn := Product.SmallerOpenProjection.Constructions.project_Thom_smaller (G := V.analyticModel) U (Cycle.GoodOpenMap.Constructions.goodNeighborhood D W U) inf_le_left i hi
    ((Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion) K hii hc p hp hK hT
  have hb := Product.SmallerOpenProjection.Constructions.smallerGraph_bound U (Cycle.GoodOpenMap.Constructions.goodNeighborhood D W U) inf_le_left i hi
    ((Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion) K hT
  have ht := Cycle.OpenProjectionSupport.Constructions.graphThom_project_openCycleClass D (Cycle.GoodOpenMap.Constructions.goodNeighborhood D W U) (retainedRegular D W hWs U)
    (retainedGraph D W U i hi) (Product.SmallerOpen.Constructions.smallerGraph_analytic U (Cycle.GoodOpenMap.Constructions.goodNeighborhood D W U) inf_le_left i hi)
    (Product.SmallerOpen.Constructions.smallerGraph_differential_injective U (Cycle.GoodOpenMap.Constructions.goodNeighborhood D W U) inf_le_left i hi hii)
    (Product.SmallerOpen.Constructions.smallerGraph_closedEmbedding U (Cycle.GoodOpenMap.Constructions.goodNeighborhood D W U) inf_le_left i hi hc)
    hp K hK hb hip hfin m hdeg
  exact hn.symm.trans ht

end

end OAI.AlgebraicGeometry.CycleClass.Thom.GenericGraph.Constructions.Class
