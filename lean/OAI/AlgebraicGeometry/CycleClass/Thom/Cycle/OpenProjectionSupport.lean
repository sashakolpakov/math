import OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularOpenProjection
import OAI.AlgebraicGeometry.CycleClass.Thom.Projection.TargetSupport

/-! # Open Projection Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.OpenProjectionSupport.Constructions

noncomputable section

/-! On a regular ambient open, finite graph Thom projection equals the original restricted supported cycle class with its original support presentation. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularOpenProjection.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularNeighborhoodDetection.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Projection.TargetSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup.Constructions.Restriction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (U : Opens V.analyticSpace) (hU : (U : Set V.analyticSpace) ⊆ D.regularAmbientOpen)
  {L E : Type} [TopologicalSpace L] [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [ChartedSpace E L] [IsManifold 𝓘(ℂ, E) ω L] {d : ℕ}

local instance : MetrizableSpace U := U.isOpenEmbedding'.isEmbedding.metrizableSpace
local instance (priority := low) : ChartedSpace (V.analyticModel × (Fin d → ℂ)) (U × (Fin d → ℂ)) :=
  prodChartedSpace V.analyticModel U (Fin d → ℂ) (Fin d → ℂ)
local instance : IsManifold 𝓘(ℂ, V.analyticModel × (Fin d → ℂ)) ω (U × (Fin d → ℂ)) :=
  Product.Immersion.Constructions.productModel_isManifold

theorem graphThom_project_openCycleClass
    (i : L → U × (Fin d → ℂ)) (hi : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, V.analyticModel × (Fin d → ℂ)) ω i)
    (hii : ∀ y, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, V.analyticModel × (Fin d → ℂ)) i y))
    (hc : Topology.IsClosedEmbedding i) (hp : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E (V.analyticModel × (Fin d → ℂ)) = p + d)
    (K : Set (Fin d → ℂ)) (hK : IsCompact K)
    (hT : Set.range i ⊆ ((Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion) ×ˢ K)
    (hip : ∀ y, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, V.analyticModel) (Prod.fst ∘ i) y))
    (hfin : ∀ x : GraphOpenImmersion.Constructions.graphSourceOpen D.regularComplementInclusion (D.contMDiff_regularComplementInclusion ω)
      (RegularNeighborhoodDetection.Constructions.regularNeighborhood D U), Finite {y : L | (i y).1 = RegularOpenImmersion.Constructions.regularOpenImmersion D U hU x})
    (m : ℕ) (hdeg : ∀ x : GraphOpenImmersion.Constructions.graphSourceOpen D.regularComplementInclusion (D.contMDiff_regularComplementInclusion ω)
      (RegularNeighborhoodDetection.Constructions.regularNeighborhood D U), Nat.card {y : L | (i y).1 = RegularOpenImmersion.Constructions.regularOpenImmersion D U hU x} = m) :
    Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of U) ((Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion)
      K hK (Set.range i) hT (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm
      (Degree.Constructions.ThomClass.complexThomClassInDegree i hi hii hc (p + d) hp) =
      (m : ℚ) • Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
        (Set.range D.analyticInclusion)ᶜ U (2 * p) D.rationalSupportedCycleClass := by
  have hr := RegularOpenImmersion.Constructions.regularOpenImmersion_range D U hU
  have hTf : Set.range i ⊆ Set.range (RegularOpenImmersion.Constructions.regularOpenImmersion D U hU) ×ˢ K := by rwa [hr]
  have h := RegularOpenProjection.Constructions.graphThom_project_cycleClass D U hU i hi hii hc hp K hK hTf hip hfin m hdeg
  let F := eqToHom (congrArg (fun A => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) Aᶜ (2 * p)) hr)
  have ht := Projection.TargetSupport.Constructions.projectAt_targetCast d (TopCat.of U) (Set.range (RegularOpenImmersion.Constructions.regularOpenImmersion D U hU))
    ((Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion) hr K hK (Set.range i) hTf hT
    (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm (Degree.Constructions.ThomClass.complexThomClassInDegree i hi hii hc (p + d) hp)
  have hs := ExteriorImageCup.Constructions.Restriction.relativeCohomologyMap_sourceCast
    (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (U : Set V.analyticSpace)) (congrArg Set.compl hr)
    (RegularOpenImmersion.Constructions.regularOpenImmersion_mapsTo D U hU) (fun _ hx => hx) (2 * p) D.rationalSupportedCycleClass
  have hm : F ((m : ℚ) • AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (U : Set V.analyticSpace))
      (RegularOpenImmersion.Constructions.regularOpenImmersion_mapsTo D U hU) (2 * p) D.rationalSupportedCycleClass) =
      (m : ℚ) • Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
        (Set.range D.analyticInclusion)ᶜ U (2 * p) D.rationalSupportedCycleClass := by
    rw [map_smul]
    exact congrArg (fun a => (m : ℚ) • a) hs
  exact ht.symm.trans ((congrArg (fun a => F a) h).trans hm)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.OpenProjectionSupport.Constructions
