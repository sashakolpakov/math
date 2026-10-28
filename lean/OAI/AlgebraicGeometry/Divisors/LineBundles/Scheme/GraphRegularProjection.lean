import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.RegularOpenThom
import OAI.AlgebraicGeometry.CycleClass.Thom.Finite.Projection

/-! # Graph Regular Projection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.GraphRegularProjection.BundleCycles

noncomputable section

/-! On a regular ambient open, a genuine bounded finite unramified graph projects its Thom class to its actual fiber degree times the original supported cycle class. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Finite.Projection.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass
open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (Z : IrreducibleCloseds X.left) (p : ℕ)
  (hpZ : Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ⊆ CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z)
  {L W : Type} [TopologicalSpace L] [NormedAddCommGroup W] [NormedSpace ℂ W]
  [FiniteDimensional ℂ W] [ChartedSpace W L] [IsManifold 𝓘(ℂ, W) ω L] {d : ℕ}

local instance e13SchemeGraphRegularProjection_local1 : MetrizableSpace U := U.isOpenEmbedding'.isEmbedding.metrizableSpace
local instance (priority := low) e13SchemeGraphRegularProjection_local2 : ChartedSpace ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) × (Fin d → ℂ)) (U × (Fin d → ℂ)) :=
  prodChartedSpace (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) U (Fin d → ℂ) (Fin d → ℂ)
local instance e13SchemeGraphRegularProjection_local3 : IsManifold 𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) × (Fin d → ℂ)) ω (U × (Fin d → ℂ)) :=
  CycleClass.Thom.Product.Immersion.Constructions.productModel_isManifold

theorem schemeGraphThom_project_cycleClass
    (i : L → U × (Fin d → ℂ)) (hi : ContMDiff 𝓘(ℂ, W) 𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) × (Fin d → ℂ)) ω i)
    (hii : ∀ y, Function.Injective (mfderiv 𝓘(ℂ, W) 𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) × (Fin d → ℂ)) i y))
    (he : Topology.IsClosedEmbedding i) (hp : CycleClass.Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension W ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) × (Fin d → ℂ)) = p + d)
    (K : Set (Fin d → ℂ)) (hK : IsCompact K)
    (hT : Set.range i ⊆ Set.range (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion X Z U hU) ×ˢ K)
    (hip : ∀ y, Function.Injective (mfderiv 𝓘(ℂ, W) 𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) (Prod.fst ∘ i) y))
    (hfin : ∀ x : CycleClass.Thom.GraphOpenImmersion.Constructions.graphSourceOpen (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X Z) (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_contMDiff X Z ω)
      (SupportNeighborhoodDetection.BundleCycles.schemeSupportRegularNeighborhood X Z U), Finite {y : L | (i y).1 = SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion X Z U hU x})
    (m : ℕ) (hdeg : ∀ x : CycleClass.Thom.GraphOpenImmersion.Constructions.graphSourceOpen (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X Z) (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_contMDiff X Z ω)
      (SupportNeighborhoodDetection.BundleCycles.schemeSupportRegularNeighborhood X Z U), Nat.card {y : L | (i y).1 = SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion X Z U hU x} = m) :
    CycleClass.Thom.Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of U) (Set.range (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion X Z U hU)) K hK (Set.range i) hT
      (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm (CycleClass.Thom.Degree.Constructions.ThomClass.complexThomClassInDegree i hi hii he (p + d) hp) =
      (m : ℚ) • AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
        (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion_mapsTo X Z U hU) (2 * p) (SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X Z p hpZ) := by
  have h := CycleClass.Thom.Finite.Projection.Constructions.ThomClass.project_ThomClass (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion X Z U hU) (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion_analytic X Z U hU)
    (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion_differential_injective X Z U hU) (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion_closedEmbedding X Z U hU)
    (SupportedCycleClass.BundleCycles.schemeRegularSupportCodimension X Z p hpZ) i hi hii he hp K hK hT hip hfin m hdeg
  exact h.trans (congrArg (fun a => (m : ℚ) • a) (SchemeCycle.RegularOpenThom.BundleCycles.schemeSupportedCycleClass_regularOpen_Thom X Z U hU p hpZ).symm)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.GraphRegularProjection.BundleCycles
