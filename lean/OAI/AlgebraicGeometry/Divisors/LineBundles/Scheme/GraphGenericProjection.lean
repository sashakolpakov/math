import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.GraphOpenProjection
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportGoodOpenMap
import OAI.AlgebraicGeometry.CycleClass.Thom.Product.SmallerOpenProjection

/-! # Graph Generic Projection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.GraphGenericProjection.BundleCycles

noncomputable section

/-! A bounded closed holomorphic graph over an arbitrary cycle projects to its generic fiber degree times the original supported cycle class. Finiteness and unramifiedness are needed only on a dense smooth support open; actual purity extends the equality across its omitted boundary. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Product.SmallerOpen.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Product.SmallerOpenProjection.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.SubsetHomeomorph.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.ProductHomeomorphAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (Z : IrreducibleCloseds X.left) (p : ℕ)
  (hpZ : Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
  (W : (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z).Opens) (hWs : W ≤ (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z X.hom).smoothLocus)
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))

include hWs in
omit [AlgebraicGeometry.IsIntegral X.left] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeGraphRetained_regular :
    (SupportGoodOpenMap.BundleCycles.schemeSupportGoodNeighborhood X Z W U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ⊆ CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z := by
  intro x hx hbad
  obtain ⟨y, hy, he⟩ := hbad
  exact hx.2 ⟨y, fun h => hy (hWs h), he⟩

variable {L E : Type} [TopologicalSpace L] [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedSpace ℝ E] [ChartedSpace E L] [IsManifold 𝓘(ℂ, E) ω L] {d : ℕ}

local instance e13SchemeGraphGenericProjection_local1 (A : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) : MetrizableSpace A := A.isOpenEmbedding'.isEmbedding.metrizableSpace
local instance (priority := low) e13SchemeGraphGenericProjection_local2 (A : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) :
    ChartedSpace ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) × (Fin d → ℂ)) (A × (Fin d → ℂ)) :=
  prodChartedSpace (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) A (Fin d → ℂ) (Fin d → ℂ)
local instance e13SchemeGraphGenericProjection_local3 (A : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) : IsManifold 𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) × (Fin d → ℂ)) ω (A × (Fin d → ℂ)) :=
  CycleClass.Thom.Product.Immersion.Constructions.productModel_isManifold

variable (i : L → U × (Fin d → ℂ)) (hi : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) × (Fin d → ℂ)) ω i)

abbrev schemeGraphRetainedSource := CycleClass.Thom.GraphOpenImmersion.Constructions.graphSourceOpen i hi (CycleClass.Thom.Open.ProductHomeomorphAnalytic.Constructions.productBaseOpen (CycleClass.Thom.Open.SubsetHomeomorph.Constructions.insideOpen U (SupportGoodOpenMap.BundleCycles.schemeSupportGoodNeighborhood X Z W U)))

def schemeGraphRetainedGraph : schemeGraphRetainedSource X Z W U i hi → SupportGoodOpenMap.BundleCycles.schemeSupportGoodNeighborhood X Z W U × (Fin d → ℂ) :=
  CycleClass.Thom.Product.SmallerOpen.Constructions.smallerGraph U (SupportGoodOpenMap.BundleCycles.schemeSupportGoodNeighborhood X Z W U) inf_le_left i hi

theorem schemeGraphThom_project_genericCycleClass (hW : genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z) ∈ W)
    (hii : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) × (Fin d → ℂ)) i x))
    (hc : Topology.IsClosedEmbedding i) (hp : CycleClass.Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) × (Fin d → ℂ)) = p + d)
    (K : Set (Fin d → ℂ)) (hK : IsCompact K)
    (hT : Set.range i ⊆ ((Subtype.val : U → (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z)) ×ˢ K)
    (hip : ∀ x : schemeGraphRetainedSource X Z W U i hi,
      Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) (Prod.fst ∘ schemeGraphRetainedGraph X Z W U i hi) x))
    (hfin : ∀ x : CycleClass.Thom.GraphOpenImmersion.Constructions.graphSourceOpen (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X Z) (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_contMDiff X Z ω)
      (SupportNeighborhoodDetection.BundleCycles.schemeSupportRegularNeighborhood X Z (SupportGoodOpenMap.BundleCycles.schemeSupportGoodNeighborhood X Z W U)),
      Finite {y : schemeGraphRetainedSource X Z W U i hi | (schemeGraphRetainedGraph X Z W U i hi y).1 =
        SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion X Z (SupportGoodOpenMap.BundleCycles.schemeSupportGoodNeighborhood X Z W U) (schemeGraphRetained_regular X Z W hWs U) x})
    (m : ℕ) (hdeg : ∀ x : CycleClass.Thom.GraphOpenImmersion.Constructions.graphSourceOpen (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X Z) (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_contMDiff X Z ω)
      (SupportNeighborhoodDetection.BundleCycles.schemeSupportRegularNeighborhood X Z (SupportGoodOpenMap.BundleCycles.schemeSupportGoodNeighborhood X Z W U)),
      Nat.card {y : schemeGraphRetainedSource X Z W U i hi | (schemeGraphRetainedGraph X Z W U i hi y).1 =
        SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion X Z (SupportGoodOpenMap.BundleCycles.schemeSupportGoodNeighborhood X Z W U) (schemeGraphRetained_regular X Z W hWs U) x} = m) :
    CycleClass.Thom.Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of U) ((Subtype.val : U → (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))
      K hK (Set.range i) hT (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm
      (CycleClass.Thom.Degree.Constructions.ThomClass.complexThomClassInDegree i hi hii hc (p + d) hp) =
      (m : ℚ) • CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
        (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))ᶜ U (2 * p) (SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X Z p hpZ) := by
  apply SupportGoodOpenMap.BundleCycles.schemeSupportGoodOpenPullback_injective X Z W U p hpZ hW
  rw [map_smul, SupportGoodOpenMap.BundleCycles.schemeSupportGoodOpenPullback_cycleClass]
  have hn := CycleClass.Thom.Product.SmallerOpenProjection.Constructions.project_Thom_smaller (G := (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) U (SupportGoodOpenMap.BundleCycles.schemeSupportGoodNeighborhood X Z W U) inf_le_left i hi
    ((Subtype.val : U → (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z)) K hii hc p hp hK hT
  have hb := CycleClass.Thom.Product.SmallerOpenProjection.Constructions.smallerGraph_bound U (SupportGoodOpenMap.BundleCycles.schemeSupportGoodNeighborhood X Z W U) inf_le_left i hi
    ((Subtype.val : U → (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z)) K hT
  have ht := GraphOpenProjection.BundleCycles.schemeGraphThom_project_openCycleClass X Z p hpZ (SupportGoodOpenMap.BundleCycles.schemeSupportGoodNeighborhood X Z W U) (schemeGraphRetained_regular X Z W hWs U)
    (schemeGraphRetainedGraph X Z W U i hi) (CycleClass.Thom.Product.SmallerOpen.Constructions.smallerGraph_analytic U (SupportGoodOpenMap.BundleCycles.schemeSupportGoodNeighborhood X Z W U) inf_le_left i hi)
    (CycleClass.Thom.Product.SmallerOpen.Constructions.smallerGraph_differential_injective U (SupportGoodOpenMap.BundleCycles.schemeSupportGoodNeighborhood X Z W U) inf_le_left i hi hii)
    (CycleClass.Thom.Product.SmallerOpen.Constructions.smallerGraph_closedEmbedding U (SupportGoodOpenMap.BundleCycles.schemeSupportGoodNeighborhood X Z W U) inf_le_left i hi hc)
    hp K hK hb hip hfin m hdeg
  exact hn.symm.trans ht

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.GraphGenericProjection.BundleCycles
