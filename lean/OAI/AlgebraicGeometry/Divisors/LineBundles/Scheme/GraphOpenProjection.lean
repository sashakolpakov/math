import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.GraphRegularProjection
import OAI.AlgebraicGeometry.CycleClass.Thom.Projection.TargetSupport

/-! # Graph Open Projection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.GraphOpenProjection.BundleCycles

noncomputable section

/-! On a regular ambient open, finite graph Thom projection equals the original restricted supported cycle class with its original support presentation. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Projection.TargetSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup.Constructions.Restriction

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (Z : IrreducibleCloseds X.left) (p : ℕ)
  (hpZ : Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ⊆ CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z)
  {L E : Type} [TopologicalSpace L] [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [ChartedSpace E L] [IsManifold 𝓘(ℂ, E) ω L] {d : ℕ}

local instance e13SchemeGraphOpenProjection_local1 : MetrizableSpace U := U.isOpenEmbedding'.isEmbedding.metrizableSpace
local instance (priority := low) e13SchemeGraphOpenProjection_local2 : ChartedSpace ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) × (Fin d → ℂ)) (U × (Fin d → ℂ)) :=
  prodChartedSpace (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) U (Fin d → ℂ) (Fin d → ℂ)
local instance e13SchemeGraphOpenProjection_local3 : IsManifold 𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) × (Fin d → ℂ)) ω (U × (Fin d → ℂ)) :=
  CycleClass.Thom.Product.Immersion.Constructions.productModel_isManifold

theorem schemeGraphThom_project_openCycleClass
    (i : L → U × (Fin d → ℂ)) (hi : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) × (Fin d → ℂ)) ω i)
    (hii : ∀ y, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) × (Fin d → ℂ)) i y))
    (hc : Topology.IsClosedEmbedding i) (hp : CycleClass.Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) × (Fin d → ℂ)) = p + d)
    (K : Set (Fin d → ℂ)) (hK : IsCompact K)
    (hT : Set.range i ⊆ ((Subtype.val : U → (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z)) ×ˢ K)
    (hip : ∀ y, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) (Prod.fst ∘ i) y))
    (hfin : ∀ x : CycleClass.Thom.GraphOpenImmersion.Constructions.graphSourceOpen (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X Z) (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_contMDiff X Z ω)
      (SupportNeighborhoodDetection.BundleCycles.schemeSupportRegularNeighborhood X Z U), Finite {y : L | (i y).1 = SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion X Z U hU x})
    (m : ℕ) (hdeg : ∀ x : CycleClass.Thom.GraphOpenImmersion.Constructions.graphSourceOpen (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X Z) (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_contMDiff X Z ω)
      (SupportNeighborhoodDetection.BundleCycles.schemeSupportRegularNeighborhood X Z U), Nat.card {y : L | (i y).1 = SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion X Z U hU x} = m) :
    CycleClass.Thom.Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of U) ((Subtype.val : U → (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))
      K hK (Set.range i) hT (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm
      (CycleClass.Thom.Degree.Constructions.ThomClass.complexThomClassInDegree i hi hii hc (p + d) hp) =
      (m : ℚ) • CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
        (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))ᶜ U (2 * p) (SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X Z p hpZ) := by
  have hr := SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion_range X Z U hU
  have hTf : Set.range i ⊆ Set.range (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion X Z U hU) ×ˢ K := by rwa [hr]
  have h := GraphRegularProjection.BundleCycles.schemeGraphThom_project_cycleClass X Z p hpZ U hU i hi hii hc hp K hK hTf hip hfin m hdeg
  let F := eqToHom (congrArg (fun A => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) Aᶜ (2 * p)) hr)
  have ht := CycleClass.Thom.Projection.TargetSupport.Constructions.projectAt_targetCast d (TopCat.of U) (Set.range (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion X Z U hU))
    ((Subtype.val : U → (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z)) hr K hK (Set.range i) hTf hT
    (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm (CycleClass.Thom.Degree.Constructions.ThomClass.complexThomClassInDegree i hi hii hc (p + d) hp)
  have hs := CycleClass.Thom.ExteriorImageCup.Constructions.Restriction.relativeCohomologyMap_sourceCast
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))) (congrArg Set.compl hr)
    (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion_mapsTo X Z U hU) (fun _ hx => hx) (2 * p) (SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X Z p hpZ)
  have hm : F ((m : ℚ) • AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
      (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion_mapsTo X Z U hU) (2 * p) (SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X Z p hpZ)) =
      (m : ℚ) • CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
        (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))ᶜ U (2 * p) (SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X Z p hpZ) := by
    rw [map_smul]
    exact congrArg (fun a => (m : ℚ) • a) hs
  exact ht.symm.trans ((congrArg (fun a => F a) h).trans hm)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.GraphOpenProjection.BundleCycles
