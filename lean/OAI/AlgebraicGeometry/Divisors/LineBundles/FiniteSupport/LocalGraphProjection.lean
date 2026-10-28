import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.GraphProjection
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.EtaleLocalGraphProjection

/-! # Local Graph Projection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.LocalGraphProjection.BundleCycles

noncomputable section

/-! The actual finite support cover with local coordinates carries precisely its algebraic residue degree under supported graph projection. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.EtaleLocalGraph.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.EtaleGraphOpenImmersion.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions
open scoped _root_.Manifold ContDiff

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [LocallyOfFiniteType X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [AlgebraicGeometry.IsNoetherian Y.left]
    [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] (f : X ⟶ Y) [IsFinite f.left]
    (Z : IrreducibleCloseds X.left) (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
    (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) ⊆ Cover.BundleCycles.finiteSupportRetainedOpen f Z)

variable (p : ℕ) (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) Y.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom)
    {d : ℕ} (e : CycleClass.Thom.GraphOpenImmersion.Constructions.graphSourceOpen (CycleClass.Thom.EtaleGraphOpenImmersion.Constructions.etaleBase (Cover.BundleCycles.finiteSupportCoverMap f Z) (Cover.BundleCycles.finiteSupportTargetAmbientMap f Z))
      (CycleClass.Thom.EtaleGraphOpenImmersion.Constructions.etaleBase_analytic (Cover.BundleCycles.finiteSupportCoverMap f Z) (Cover.BundleCycles.finiteSupportTargetAmbientMap f Z)) U → Fin d → ℂ)

local instance finiteSupportLocalGraphMetrizable : MetrizableSpace U := U.isOpenEmbedding'.isEmbedding.metrizableSpace
local instance (priority := low) finiteSupportLocalGraphCharted : ChartedSpace
    ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ) × (Fin d → ℂ)) (U × (Fin d → ℂ)) :=
  prodChartedSpace (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ) U (Fin d → ℂ) (Fin d → ℂ)
local instance finiteSupportLocalGraphManifold : IsManifold
    𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ) × (Fin d → ℂ)) ω (U × (Fin d → ℂ)) :=
  CycleClass.Thom.Product.Immersion.Constructions.productModel_isManifold

omit [LocallyOfFiniteType X.hom] in
theorem finiteSupportLocalGraph_project_cycleClass
    (he : ContMDiff 𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Cover.BundleCycles.finiteSupportSourceOver f Z).hom) → ℂ)
      𝓘(ℂ, Fin d → ℂ) ω e)
    (hc : Topology.IsClosedEmbedding (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph (Cover.BundleCycles.finiteSupportCoverMap f Z) (Cover.BundleCycles.finiteSupportTargetAmbientMap f Z) U e))
    (K : Set (Fin d → ℂ)) (hK : IsCompact K)
    (hT : Set.range (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph (Cover.BundleCycles.finiteSupportCoverMap f Z) (Cover.BundleCycles.finiteSupportTargetAmbientMap f Z) U e) ⊆
      Set.range (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) U
        (hU.trans (Cover.BundleCycles.finiteSupportRetainedOpen_target_regular f Z))) ×ˢ K) :
    CycleClass.Thom.Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of U) (Set.range (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) U
      (hU.trans (Cover.BundleCycles.finiteSupportRetainedOpen_target_regular f Z)))) K hK
      (Set.range (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph (Cover.BundleCycles.finiteSupportCoverMap f Z) (Cover.BundleCycles.finiteSupportTargetAmbientMap f Z) U e)) hT
      (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm
      (CycleClass.Thom.Degree.Constructions.ThomClass.complexThomClassInDegree (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph (Cover.BundleCycles.finiteSupportCoverMap f Z) (Cover.BundleCycles.finiteSupportTargetAmbientMap f Z) U e)
        (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph_analytic (Cover.BundleCycles.finiteSupportCoverMap f Z) (Cover.BundleCycles.finiteSupportTargetAmbientMap f Z) U e he)
        (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph_differential_injective (Cover.BundleCycles.finiteSupportCoverMap f Z) (Cover.BundleCycles.finiteSupportTargetAmbientMap f Z) U e he)
        hc (p + d) (GraphProjection.BundleCycles.finiteSupportGraph_codimension f Z p hp d)) =
    (f.left.residueDegree (irreducibleSetEquivPoints Z) : ℚ) •
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)))
        (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion_mapsTo Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) U
          (hU.trans (Cover.BundleCycles.finiteSupportRetainedOpen_target_regular f Z))) (2 * p)
        (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) p hp) := by
  have h := Scheme.EtaleLocalGraphProjection.BundleCycles.schemeEtaleLocalGraph_project_cycleClass Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) p hp U
    (hU.trans (Cover.BundleCycles.finiteSupportRetainedOpen_target_regular f Z)) (Cover.BundleCycles.finiteSupportCoverMap f Z)
    (Cover.BundleCycles.finiteSupportTargetAmbientMap f Z) (Cover.BundleCycles.finiteSupportCoverMap_genericPoint f Z)
    (GraphProjection.BundleCycles.finiteSupportTargetAmbientMap_regular_range f Z U hU) e he hc (GraphProjection.BundleCycles.finiteSupportGraph_codimension f Z p hp d) K hK hT
  simpa only [Cover.BundleCycles.finiteSupportCoverMap_residueDegree] using h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.LocalGraphProjection.BundleCycles
