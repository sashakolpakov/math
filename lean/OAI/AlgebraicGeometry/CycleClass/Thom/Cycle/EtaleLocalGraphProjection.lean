import OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularOpenProjection
import OAI.AlgebraicGeometry.CycleClass.Thom.EtaleLocalGraph
import OAI.AlgebraicGeometry.CycleClass.Thom.RestrictedGraphFiber
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.IntrinsicFiberDegree
import OAI.AlgebraicGeometry.CycleClass.Thom.Integral.SchemeProper

/-! # Etale Local Graph Projection -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.EtaleLocalGraphProjection.Constructions

noncomputable section

/-! Finite étale graphs with coordinates defined only on the retained source preimage project to the original supported cycle class with the actual generic residue degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularOpenProjection.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularNeighborhoodDetection.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.EtaleLocalGraph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.EtaleGraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.RestrictedGraphFiber.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.IntrinsicFiberDegree.Constructions.Construction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (U : Opens V.analyticSpace) (hU : (U : Set V.analyticSpace) ⊆ D.regularAmbientOpen)
  {L M : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral L.left] [Smooth L.hom] [IsIntegral M.left] [Smooth M.hom]
  (g : L ⟶ M) [IsFinite g.left] [Etale g.left] (j : M ⟶ V.toOver) [IsImmersion j.left]

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)
local instance : MetrizableSpace U := U.isOpenEmbedding'.isEmbedding.metrizableSpace

local notation "ML" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension L.hom) → ℂ

variable {d : ℕ}

local instance (priority := low) : ChartedSpace
    ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension V.toOver.hom) → ℂ) × (Fin d → ℂ))
    (U × (Fin d → ℂ)) :=
  prodChartedSpace (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension V.toOver.hom) → ℂ) U (Fin d → ℂ) (Fin d → ℂ)
local instance (priority := low) : ChartedSpace (V.analyticModel × (Fin d → ℂ)) (U × (Fin d → ℂ)) :=
  prodChartedSpace V.analyticModel U (Fin d → ℂ) (Fin d → ℂ)
local instance : IsManifold 𝓘(ℂ, V.analyticModel × (Fin d → ℂ)) ω (U × (Fin d → ℂ)) :=
  Product.Immersion.Constructions.productModel_isManifold
local instance : IsManifold
    𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension V.toOver.hom) → ℂ) × (Fin d → ℂ)) ω
    (U × (Fin d → ℂ)) := Product.Immersion.Constructions.productModel_isManifold

theorem etaleLocalGraph_project_cycleClass
    (hη : g.left (genericPoint L.left) = genericPoint M.left)
    (hr : ((Subtype.val : U → V.analyticSpace) ⁻¹' Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j)) =
      Set.range (RegularOpenImmersion.Constructions.regularOpenImmersion D U hU))
    (e : GraphOpenImmersion.Constructions.graphSourceOpen (EtaleGraphOpenImmersion.Constructions.etaleBase g j) (EtaleGraphOpenImmersion.Constructions.etaleBase_analytic g j) U → (Fin d → ℂ))
    (he : ContMDiff 𝓘(ℂ, ML) 𝓘(ℂ, Fin d → ℂ) ω e)
    (hc : Topology.IsClosedEmbedding (EtaleLocalGraph.Constructions.localGraph g j U e))
    (hp : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension ML (V.analyticModel × (Fin d → ℂ)) = p + d)
    (K : Set (Fin d → ℂ)) (hK : IsCompact K)
    (hT : Set.range (EtaleLocalGraph.Constructions.localGraph g j U e) ⊆ Set.range (RegularOpenImmersion.Constructions.regularOpenImmersion D U hU) ×ˢ K) :
    Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of U) (Set.range (RegularOpenImmersion.Constructions.regularOpenImmersion D U hU)) K hK
      (Set.range (EtaleLocalGraph.Constructions.localGraph g j U e)) hT (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm
      (Degree.Constructions.ThomClass.complexThomClassInDegree (EtaleLocalGraph.Constructions.localGraph g j U e) (EtaleLocalGraph.Constructions.localGraph_analytic g j U e he)
        (EtaleLocalGraph.Constructions.localGraph_differential_injective g j U e he) hc (p + d) hp) =
      (g.left.residueDegree (genericPoint L.left) : ℚ) •
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
          (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (U : Set V.analyticSpace))
          (RegularOpenImmersion.Constructions.regularOpenImmersion_mapsTo D U hU) (2 * p) D.rationalSupportedCycleClass := by
  classical
  have htarget (x : GraphOpenImmersion.Constructions.graphSourceOpen D.regularComplementInclusion (D.contMDiff_regularComplementInclusion ω)
      (RegularNeighborhoodDetection.Constructions.regularNeighborhood D U)) :
      ∃ y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j y = (RegularOpenImmersion.Constructions.regularOpenImmersion D U hU x).val := by
    have h : RegularOpenImmersion.Constructions.regularOpenImmersion D U hU x ∈ Set.range (RegularOpenImmersion.Constructions.regularOpenImmersion D U hU) := Set.mem_range_self _
    rw [← hr] at h
    exact h
  choose target htarget using htarget
  let ef (x : GraphOpenImmersion.Constructions.graphSourceOpen D.regularComplementInclusion (D.contMDiff_regularComplementInclusion ω)
      (RegularNeighborhoodDetection.Constructions.regularNeighborhood D U)) := EtaleLocalGraph.Constructions.localGraph_fiberEquiv g j U e
        (RegularOpenImmersion.Constructions.regularOpenImmersion D U hU x) (target x) (htarget x)
  have hfin (x : GraphOpenImmersion.Constructions.graphSourceOpen D.regularComplementInclusion (D.contMDiff_regularComplementInclusion ω)
      (RegularNeighborhoodDetection.Constructions.regularNeighborhood D U)) :
      Finite {y : GraphOpenImmersion.Constructions.graphSourceOpen (EtaleGraphOpenImmersion.Constructions.etaleBase g j) (EtaleGraphOpenImmersion.Constructions.etaleBase_analytic g j) U |
        (EtaleLocalGraph.Constructions.localGraph g j U e y).1 = RegularOpenImmersion.Constructions.regularOpenImmersion D U hU x} := by
    have hf := ProperImage.Covering.Constructions.Construction.finite_fiber_of_proper_localHomeomorph (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g)
      (Integral.SchemeProper.Constructions.isProperMap_integral g)
      (ProperImage.IntrinsicEtale.Constructions.Construction.isLocalDiffeomorph_nativeScheme_affineEtale g).isLocalHomeomorph (target x)
    let : Fintype {y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints L | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g y = target x} := hf.fintype
    exact Finite.of_equiv _ (ef x).symm
  exact RegularOpenProjection.Constructions.graphThom_project_cycleClass D U hU (EtaleLocalGraph.Constructions.localGraph g j U e) (EtaleLocalGraph.Constructions.localGraph_analytic g j U e he)
    (EtaleLocalGraph.Constructions.localGraph_differential_injective g j U e he) hc hp K hK hT
    (EtaleLocalGraph.Constructions.localGraph_projected_differential_injective g j U e) hfin (g.left.residueDegree (genericPoint L.left))
    (fun x => (Nat.card_congr (ef x)).trans (ProperImage.IntrinsicFiberDegree.Constructions.Construction.native_fiber_card_eq_residueDegree g hη (target x)))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.EtaleLocalGraphProjection.Constructions
