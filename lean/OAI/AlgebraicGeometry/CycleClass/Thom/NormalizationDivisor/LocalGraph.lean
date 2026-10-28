import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.GraphOpen
import OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.EtaleLocalGraphProjection

/-! # Local Graph -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.LocalGraph.Constructions.Class

noncomputable section

/-! The graph of a normalized prime divisor with coordinates defined on its retained source open projects to the original ambient image cycle with its actual normalization residue degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Open.Constructions.Etale
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Analytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Image.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.GraphOpen.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.EtaleLocalGraphProjection.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.EtaleGraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.EtaleLocalGraph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)
  (z : {x : (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).left // Order.coheight x = 1})
  (U : Opens V.analyticSpace) (hU : (U : Set V.analyticSpace) ⊆ GraphOpen.Constructions.goodAmbient V W z)

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)
local instance : MetrizableSpace U := U.isOpenEmbedding'.isEmbedding.metrizableSpace

local notation "ML" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Over.hom (OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Open.Constructions.Etale.sourceOpen V W z))) → ℂ
local notation "q" => OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.dimensionCodimension V W + 1

variable {d : ℕ}

local instance (priority := low) : ChartedSpace (V.analyticModel × (Fin d → ℂ)) (U × (Fin d → ℂ)) :=
  prodChartedSpace V.analyticModel U (Fin d → ℂ) (Fin d → ℂ)
local instance (priority := low) : ChartedSpace
    ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension V.toOver.hom) → ℂ) × (Fin d → ℂ)) (U × (Fin d → ℂ)) :=
  prodChartedSpace (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension V.toOver.hom) → ℂ) U (Fin d → ℂ) (Fin d → ℂ)
local instance : IsManifold 𝓘(ℂ, V.analyticModel × (Fin d → ℂ)) ω (U × (Fin d → ℂ)) :=
  Product.Immersion.Constructions.productModel_isManifold
local instance : IsManifold
    𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension V.toOver.hom) → ℂ) × (Fin d → ℂ)) ω
    (U × (Fin d → ℂ)) := Product.Immersion.Constructions.productModel_isManifold

variable (e : GraphOpenImmersion.Constructions.graphSourceOpen (EtaleGraphOpenImmersion.Constructions.etaleBase (Open.Constructions.Etale.coverMap V W z) (Analytic.Constructions.targetAmbientMap V W z))
  (EtaleGraphOpenImmersion.Constructions.etaleBase_analytic (Open.Constructions.Etale.coverMap V W z) (Analytic.Constructions.targetAmbientMap V W z)) U → Fin d → ℂ) (K : Set (Fin d → ℂ))

theorem divisorLocalGraph_bound
    (hb : ∀ x, e x ∈ K) :
    Set.range (EtaleLocalGraph.Constructions.localGraph (Open.Constructions.Etale.coverMap V W z) (Analytic.Constructions.targetAmbientMap V W z) U e) ⊆
      Set.range (Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion (Image.Constructions.imageCycleSupport V W z) U (hU.trans (GraphOpen.Constructions.goodAmbient_regular V W z))) ×ˢ K := by
  rintro _ ⟨x, rfl⟩
  refine ⟨?_, hb x⟩
  rw [← GraphOpen.Constructions.targetAmbientMap_range V W z U hU]
  exact ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Open.Constructions.Etale.coverMap V W z) x.val, rfl⟩

theorem divisorLocalGraph_project_imageCycleClass
    (he : ContMDiff 𝓘(ℂ, ML) 𝓘(ℂ, Fin d → ℂ) ω e)
    (hc : Topology.IsClosedEmbedding (EtaleLocalGraph.Constructions.localGraph (Open.Constructions.Etale.coverMap V W z) (Analytic.Constructions.targetAmbientMap V W z) U e))
    (hK : IsCompact K)
    (hb : ∀ x, e x ∈ K) :
    Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of U)
      (Set.range (Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion (Image.Constructions.imageCycleSupport V W z) U (hU.trans (GraphOpen.Constructions.goodAmbient_regular V W z)))) K hK
      (Set.range (EtaleLocalGraph.Constructions.localGraph (Open.Constructions.Etale.coverMap V W z) (Analytic.Constructions.targetAmbientMap V W z) U e)) (divisorLocalGraph_bound V W z U hU e K hb)
      (2 * q) (2 * (q + d)) (Nat.mul_add 2 q d).symm
      (Degree.Constructions.ThomClass.complexThomClassInDegree (EtaleLocalGraph.Constructions.localGraph (Open.Constructions.Etale.coverMap V W z) (Analytic.Constructions.targetAmbientMap V W z) U e)
        (EtaleLocalGraph.Constructions.localGraph_analytic (Open.Constructions.Etale.coverMap V W z) (Analytic.Constructions.targetAmbientMap V W z) U e he)
        (EtaleLocalGraph.Constructions.localGraph_differential_injective (Open.Constructions.Etale.coverMap V W z) (Analytic.Constructions.targetAmbientMap V W z) U e he)
        hc (q + d) (GraphOpen.Constructions.sourceGraph_codimension V W z d)) =
      ((Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W).left.residueDegree z.val : ℚ) •
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
          (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (U : Set V.analyticSpace))
          (Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion_mapsTo (Image.Constructions.imageCycleSupport V W z) U (hU.trans (GraphOpen.Constructions.goodAmbient_regular V W z))) (2 * q)
          (Image.Constructions.imageCycleSupport V W z).rationalSupportedCycleClass := by
  have h := Cycle.EtaleLocalGraphProjection.Constructions.etaleLocalGraph_project_cycleClass (Image.Constructions.imageCycleSupport V W z) U (hU.trans (GraphOpen.Constructions.goodAmbient_regular V W z))
    (Open.Constructions.Etale.coverMap V W z) (Analytic.Constructions.targetAmbientMap V W z) (Open.Constructions.Etale.coverMap_genericPoint V W z)
    (GraphOpen.Constructions.targetAmbientMap_range V W z U hU) e he hc (GraphOpen.Constructions.sourceGraph_codimension V W z d) K hK
    (divisorLocalGraph_bound V W z U hU e K hb)
  simpa only [Open.Constructions.Etale.coverMap_residueDegree] using h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.LocalGraph.Constructions.Class
