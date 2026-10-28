import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.EtaleGraphProjection
import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.Cover
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportDenseOpenImage

/-! # Graph Projection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.GraphProjection.BundleCycles

noncomputable section

/-! The graph of the actual finite support cover projects to the
original image cycle class with precisely the original residue-field degree. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.EtaleGraphOpenImmersion.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions
open scoped _root_.Manifold ContDiff

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [LocallyOfFiniteType X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [AlgebraicGeometry.IsNoetherian Y.left]
    [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] (f : X ⟶ Y) [IsFinite f.left]
    (Z : IrreducibleCloseds X.left) (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
    (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) ⊆ Cover.BundleCycles.finiteSupportRetainedOpen f Z)

omit [LocallyOfFiniteType X.hom] in
theorem finiteSupportTargetAmbientMap_regular_range :
    ((Subtype.val : U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) ⁻¹' Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Cover.BundleCycles.finiteSupportTargetAmbientMap f Z))) =
      Set.range (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) U
        (hU.trans (Cover.BundleCycles.finiteSupportRetainedOpen_target_regular f Z))) := by
  let j := CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z)) (Cover.BundleCycles.finiteSupportGoodOpen f Z)
  have hr : j.left.opensRange = Cover.BundleCycles.finiteSupportGoodOpen f Z := Scheme.Opens.opensRange_ι _
  have hU' : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) ⊆ CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen Y
      (CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.supportOpenBoundary Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) j.left.opensRange).compl := by
    rw [hr]
    exact hU
  have he : Cover.BundleCycles.finiteSupportTargetAmbientMap f Z = j ≫ CycleClass.Thom.Scheme.RegularSupport.Constructions.supportToAmbient Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) :=
    Cover.BundleCycles.finiteSupportTargetToRegular_ambient f Z
  have hh := LineBundles.Scheme.SupportDenseOpenImage.BundleCycles.schemeSupportOpenImmersion_regularImage Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) j U hU'
    (hU.trans (Cover.BundleCycles.finiteSupportRetainedOpen_target_regular f Z))
  exact (congrArg (fun k => (Subtype.val : U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) ⁻¹' Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k)) he).trans hh

omit [LocallyOfFiniteType X.hom] [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] in
theorem finiteSupportGraph_codimension (p : ℕ)
    (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) Y.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom)
    (d : ℕ) :
    CycleClass.Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Cover.BundleCycles.finiteSupportSourceOver f Z).hom) → ℂ)
      ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ) × (Fin d → ℂ)) = p + d := by
  change Module.finrank ℂ ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ) × (Fin d → ℂ)) -
    Module.finrank ℂ (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Cover.BundleCycles.finiteSupportSourceOver f Z).hom) → ℂ) = _
  simp only [Module.finrank_prod, Module.finrank_fin_fun]
  have hsource := (Cover.BundleCycles.finiteSupportCover_dimensions_eq f Z).trans (Cover.BundleCycles.finiteSupportTargetOver_dimension f Z)
  have hreg := CycleClass.Thom.Scheme.RegularSupport.Constructions.regularDimension_eq Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z)
  have hdim := Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension Y.hom
  omega

variable (p : ℕ) (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) Y.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom)
    {d : ℕ} (e : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Cover.BundleCycles.finiteSupportSourceOver f Z) → Fin d → ℂ)

local instance finiteSupportGraphMetrizable : MetrizableSpace U := U.isOpenEmbedding'.isEmbedding.metrizableSpace
local instance (priority := low) finiteSupportGraphCharted : ChartedSpace
    ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ) × (Fin d → ℂ)) (U × (Fin d → ℂ)) :=
  prodChartedSpace (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ) U (Fin d → ℂ) (Fin d → ℂ)
local instance finiteSupportGraphManifold : IsManifold
    𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ) × (Fin d → ℂ)) ω (U × (Fin d → ℂ)) :=
  CycleClass.Thom.Product.Immersion.Constructions.productModel_isManifold

omit [LocallyOfFiniteType X.hom] in
theorem finiteSupportGraph_project_cycleClass
    (he : ContMDiff 𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Cover.BundleCycles.finiteSupportSourceOver f Z).hom) → ℂ)
      𝓘(ℂ, Fin d → ℂ) ω e)
    (hc : Topology.IsClosedEmbedding (CycleClass.Thom.EtaleGraphOpenImmersion.Constructions.openGraph (Cover.BundleCycles.finiteSupportCoverMap f Z) (Cover.BundleCycles.finiteSupportTargetAmbientMap f Z) U e))
    (K : Set (Fin d → ℂ)) (hK : IsCompact K)
    (hT : Set.range (CycleClass.Thom.EtaleGraphOpenImmersion.Constructions.openGraph (Cover.BundleCycles.finiteSupportCoverMap f Z) (Cover.BundleCycles.finiteSupportTargetAmbientMap f Z) U e) ⊆
      Set.range (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) U
        (hU.trans (Cover.BundleCycles.finiteSupportRetainedOpen_target_regular f Z))) ×ˢ K) :
    CycleClass.Thom.Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of U) (Set.range (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) U
      (hU.trans (Cover.BundleCycles.finiteSupportRetainedOpen_target_regular f Z)))) K hK
      (Set.range (CycleClass.Thom.EtaleGraphOpenImmersion.Constructions.openGraph (Cover.BundleCycles.finiteSupportCoverMap f Z) (Cover.BundleCycles.finiteSupportTargetAmbientMap f Z) U e)) hT
      (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm
      (CycleClass.Thom.Degree.Constructions.ThomClass.complexThomClassInDegree (CycleClass.Thom.EtaleGraphOpenImmersion.Constructions.openGraph (Cover.BundleCycles.finiteSupportCoverMap f Z) (Cover.BundleCycles.finiteSupportTargetAmbientMap f Z) U e)
        (CycleClass.Thom.EtaleGraphOpenImmersion.Constructions.openGraph_analytic (Cover.BundleCycles.finiteSupportCoverMap f Z) (Cover.BundleCycles.finiteSupportTargetAmbientMap f Z) U e he)
        (CycleClass.Thom.EtaleGraphOpenImmersion.Constructions.openGraph_differential_injective (Cover.BundleCycles.finiteSupportCoverMap f Z) (Cover.BundleCycles.finiteSupportTargetAmbientMap f Z) U e he)
        hc (p + d) (finiteSupportGraph_codimension f Z p hp d)) =
    (f.left.residueDegree (irreducibleSetEquivPoints Z) : ℚ) •
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)))
        (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion_mapsTo Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) U
          (hU.trans (Cover.BundleCycles.finiteSupportRetainedOpen_target_regular f Z))) (2 * p)
        (LineBundles.Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) p hp) := by
  have h := LineBundles.Scheme.EtaleGraphProjection.BundleCycles.schemeEtaleGraph_project_cycleClass Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) p hp U
    (hU.trans (Cover.BundleCycles.finiteSupportRetainedOpen_target_regular f Z)) (Cover.BundleCycles.finiteSupportCoverMap f Z)
    (Cover.BundleCycles.finiteSupportTargetAmbientMap f Z) (Cover.BundleCycles.finiteSupportCoverMap_genericPoint f Z)
    (finiteSupportTargetAmbientMap_regular_range f Z U hU) e he hc (finiteSupportGraph_codimension f Z p hp d) K hK hT
  simpa only [Cover.BundleCycles.finiteSupportCoverMap_residueDegree] using h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.GraphProjection.BundleCycles
