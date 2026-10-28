import OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularOpenImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.Finite.Projection

/-! # Regular Open Projection -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularOpenProjection.Constructions

noncomputable section

/-! On a regular ambient open, a genuine bounded finite unramified graph projects its Thom class to its actual fiber degree times the original supported cycle class. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularNeighborhoodDetection.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Finite.Projection.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (U : Opens V.analyticSpace) (hU : (U : Set V.analyticSpace) ⊆ D.regularAmbientOpen)
  {L W : Type} [TopologicalSpace L] [NormedAddCommGroup W] [NormedSpace ℂ W]
  [FiniteDimensional ℂ W] [ChartedSpace W L] [IsManifold 𝓘(ℂ, W) ω L] {d : ℕ}

local instance : MetrizableSpace U := U.isOpenEmbedding'.isEmbedding.metrizableSpace
local instance (priority := low) : ChartedSpace (V.analyticModel × (Fin d → ℂ)) (U × (Fin d → ℂ)) :=
  prodChartedSpace V.analyticModel U (Fin d → ℂ) (Fin d → ℂ)
local instance : IsManifold 𝓘(ℂ, V.analyticModel × (Fin d → ℂ)) ω (U × (Fin d → ℂ)) :=
  Product.Immersion.Constructions.productModel_isManifold

theorem graphThom_project_cycleClass
    (i : L → U × (Fin d → ℂ)) (hi : ContMDiff 𝓘(ℂ, W) 𝓘(ℂ, V.analyticModel × (Fin d → ℂ)) ω i)
    (hii : ∀ y, Function.Injective (mfderiv 𝓘(ℂ, W) 𝓘(ℂ, V.analyticModel × (Fin d → ℂ)) i y))
    (he : Topology.IsClosedEmbedding i) (hp : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension W (V.analyticModel × (Fin d → ℂ)) = p + d)
    (K : Set (Fin d → ℂ)) (hK : IsCompact K)
    (hT : Set.range i ⊆ Set.range (RegularOpenImmersion.Constructions.regularOpenImmersion D U hU) ×ˢ K)
    (hip : ∀ y, Function.Injective (mfderiv 𝓘(ℂ, W) 𝓘(ℂ, V.analyticModel) (Prod.fst ∘ i) y))
    (hfin : ∀ x : GraphOpenImmersion.Constructions.graphSourceOpen D.regularComplementInclusion (D.contMDiff_regularComplementInclusion ω)
      (RegularNeighborhoodDetection.Constructions.regularNeighborhood D U), Finite {y : L | (i y).1 = RegularOpenImmersion.Constructions.regularOpenImmersion D U hU x})
    (m : ℕ) (hdeg : ∀ x : GraphOpenImmersion.Constructions.graphSourceOpen D.regularComplementInclusion (D.contMDiff_regularComplementInclusion ω)
      (RegularNeighborhoodDetection.Constructions.regularNeighborhood D U), Nat.card {y : L | (i y).1 = RegularOpenImmersion.Constructions.regularOpenImmersion D U hU x} = m) :
    Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of U) (Set.range (RegularOpenImmersion.Constructions.regularOpenImmersion D U hU)) K hK (Set.range i) hT
      (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm (Degree.Constructions.ThomClass.complexThomClassInDegree i hi hii he (p + d) hp) =
      (m : ℚ) • AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (U : Set V.analyticSpace))
        (RegularOpenImmersion.Constructions.regularOpenImmersion_mapsTo D U hU) (2 * p) D.rationalSupportedCycleClass := by
  have h := Thom.Finite.Projection.Constructions.ThomClass.project_ThomClass (RegularOpenImmersion.Constructions.regularOpenImmersion D U hU) (RegularOpenImmersion.Constructions.regularOpenImmersion_analytic D U hU)
    (RegularOpenImmersion.Constructions.regularOpenImmersion_differential_injective D U hU) (RegularOpenImmersion.Constructions.regularOpenImmersion_closedEmbedding D U hU)
    D.regularComplement_complexImmersionCodimension i hi hii he hp K hK hT hip hfin m hdeg
  exact h.trans (congrArg (fun a => (m : ℚ) • a) (RegularOpenImmersion.Constructions.supportedCycleClass_regularOpen_Thom D U hU).symm)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularOpenProjection.Constructions
