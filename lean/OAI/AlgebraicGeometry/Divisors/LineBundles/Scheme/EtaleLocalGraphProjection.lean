import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.GraphRegularProjection
import OAI.AlgebraicGeometry.CycleClass.Thom.EtaleLocalGraph
import OAI.AlgebraicGeometry.CycleClass.Thom.RestrictedGraphFiber
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.IntrinsicFiberDegree
import OAI.AlgebraicGeometry.CycleClass.Thom.Integral.SchemeProper

/-! # Etale Local Graph Projection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.EtaleLocalGraphProjection.BundleCycles

noncomputable section

/-! Actual finite étale scheme graphs with coordinates on the retained source open project to the original supported cycle class with their genuine generic residue degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.EtaleLocalGraph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.EtaleGraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.RestrictedGraphFiber.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.IntrinsicFiberDegree.Constructions.Construction

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (Z : IrreducibleCloseds X.left) (p : ℕ)
  (hpZ : Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ⊆ CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z)
  {L M : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral L.left] [Smooth L.hom] [IsIntegral M.left] [Smooth M.hom]
  (g : L ⟶ M) [IsFinite g.left] [Etale g.left] (j : M ⟶ X) [IsImmersion j.left]

local instance e13SchemeEtaleLocalGraphProjection_local1 : MetrizableSpace U := U.isOpenEmbedding'.isEmbedding.metrizableSpace

local notation "ML" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension L.hom) → ℂ

variable {d : ℕ}

local instance (priority := low) e13SchemeEtaleLocalGraphProjection_local2 : ChartedSpace
    ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) × (Fin d → ℂ)) (U × (Fin d → ℂ)) :=
  prodChartedSpace (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) U (Fin d → ℂ) (Fin d → ℂ)
local instance e13SchemeEtaleLocalGraphProjection_local3 : IsManifold
    𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) × (Fin d → ℂ)) ω (U × (Fin d → ℂ)) :=
  CycleClass.Thom.Product.Immersion.Constructions.productModel_isManifold

theorem schemeEtaleLocalGraph_project_cycleClass
    (hη : g.left (genericPoint L.left) = genericPoint M.left)
    (hr : ((Subtype.val : U → (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ⁻¹' Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j)) =
      Set.range (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion X Z U hU))
    (e : CycleClass.Thom.GraphOpenImmersion.Constructions.graphSourceOpen (CycleClass.Thom.EtaleGraphOpenImmersion.Constructions.etaleBase g j) (CycleClass.Thom.EtaleGraphOpenImmersion.Constructions.etaleBase_analytic g j) U → (Fin d → ℂ))
    (he : ContMDiff 𝓘(ℂ, ML) 𝓘(ℂ, Fin d → ℂ) ω e)
    (hc : Topology.IsClosedEmbedding (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph g j U e))
    (hp : CycleClass.Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension ML ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) × (Fin d → ℂ)) = p + d)
    (K : Set (Fin d → ℂ)) (hK : IsCompact K)
    (hT : Set.range (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph g j U e) ⊆ Set.range (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion X Z U hU) ×ˢ K) :
    CycleClass.Thom.Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of U) (Set.range (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion X Z U hU)) K hK
      (Set.range (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph g j U e)) hT (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm
      (CycleClass.Thom.Degree.Constructions.ThomClass.complexThomClassInDegree (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph g j U e) (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph_analytic g j U e he)
        (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph_differential_injective g j U e he) hc (p + d) hp) =
      (g.left.residueDegree (genericPoint L.left) : ℚ) •
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
          (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
          (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion_mapsTo X Z U hU) (2 * p) (SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X Z p hpZ) := by
  classical
  have htarget (x : CycleClass.Thom.GraphOpenImmersion.Constructions.graphSourceOpen (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X Z) (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_contMDiff X Z ω)
      (SupportNeighborhoodDetection.BundleCycles.schemeSupportRegularNeighborhood X Z U)) :
      ∃ y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j y = (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion X Z U hU x).val := by
    have h : SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion X Z U hU x ∈ Set.range (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion X Z U hU) := Set.mem_range_self _
    rw [← hr] at h
    exact h
  choose target htarget using htarget
  let ef (x : CycleClass.Thom.GraphOpenImmersion.Constructions.graphSourceOpen (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X Z) (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_contMDiff X Z ω)
      (SupportNeighborhoodDetection.BundleCycles.schemeSupportRegularNeighborhood X Z U)) := CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph_fiberEquiv g j U e
        (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion X Z U hU x) (target x) (htarget x)
  have hfin (x : CycleClass.Thom.GraphOpenImmersion.Constructions.graphSourceOpen (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X Z) (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_contMDiff X Z ω)
      (SupportNeighborhoodDetection.BundleCycles.schemeSupportRegularNeighborhood X Z U)) :
      Finite {y : CycleClass.Thom.GraphOpenImmersion.Constructions.graphSourceOpen (CycleClass.Thom.EtaleGraphOpenImmersion.Constructions.etaleBase g j) (CycleClass.Thom.EtaleGraphOpenImmersion.Constructions.etaleBase_analytic g j) U |
        (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph g j U e y).1 = SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion X Z U hU x} := by
    have hf := CycleClass.Thom.ProperImage.Covering.Constructions.Construction.finite_fiber_of_proper_localHomeomorph (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g)
      (CycleClass.Thom.Integral.SchemeProper.Constructions.isProperMap_integral g)
      (CycleClass.Thom.ProperImage.IntrinsicEtale.Constructions.Construction.isLocalDiffeomorph_nativeScheme_affineEtale g).isLocalHomeomorph (target x)
    let : Fintype {y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints L | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g y = target x} := hf.fintype
    exact Finite.of_equiv _ (ef x).symm
  exact GraphRegularProjection.BundleCycles.schemeGraphThom_project_cycleClass X Z p hpZ U hU (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph g j U e) (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph_analytic g j U e he)
    (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph_differential_injective g j U e he) hc hp K hK hT
    (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph_projected_differential_injective g j U e) hfin (g.left.residueDegree (genericPoint L.left))
    (fun x => (Nat.card_congr (ef x)).trans (CycleClass.Thom.ProperImage.IntrinsicFiberDegree.Constructions.Construction.native_fiber_card_eq_residueDegree g hη (target x)))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.EtaleLocalGraphProjection.BundleCycles
