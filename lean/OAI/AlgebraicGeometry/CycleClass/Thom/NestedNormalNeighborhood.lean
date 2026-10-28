import OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.SourceNeighborhood
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.IntersectionCoordinates
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition

/-! # Nested Normal Neighborhood -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NestedNormalNeighborhood.Constructions

noncomputable section

/-! Every nested pair of closed complex immersions has an actual
outer normal neighborhood contained in an inner normal source chart. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions.ComplexManifold OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.SourceNeighborhood.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.IntersectionCoordinates.Constructions

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p q : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
  (C : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion (Open.ClosedImmersionComposition.Constructions.ComplexManifold.sourceManifold Z) q) (z : C.regularAnalyticSpace)

def nestedOuterPair : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin p → ℂ)
    Z.regularComplementInclusion (C.regularComplementInclusion z) :=
  Classical.choose (NormalPair.SourceNeighborhood.Constructions.exists_subpair_source_subset
    (Z.regularFixedNormalPair (C.regularComplementInclusion z)) Z.closed.isEmbedding
    (C.regularFixedNormalPair z).openNeighborhood (C.regularFixedNormalPair z).point_mem_neighborhood)

theorem nestedOuterPair_chart : (nestedOuterPair Z C z).ambientChart =
    (Z.regularFixedNormalPair (C.regularComplementInclusion z)).ambientChart :=
  (Classical.choose_spec (NormalPair.SourceNeighborhood.Constructions.exists_subpair_source_subset
    (Z.regularFixedNormalPair (C.regularComplementInclusion z)) Z.closed.isEmbedding
    (C.regularFixedNormalPair z).openNeighborhood (C.regularFixedNormalPair z).point_mem_neighborhood)).1

theorem nestedOuterPair_source_subset :
    Z.regularComplementInclusion ⁻¹' (nestedOuterPair Z C z).neighborhood ⊆
      (C.regularFixedNormalPair z).neighborhood :=
  (Classical.choose_spec (NormalPair.SourceNeighborhood.Constructions.exists_subpair_source_subset
    (Z.regularFixedNormalPair (C.regularComplementInclusion z)) Z.closed.isEmbedding
    (C.regularFixedNormalPair z).openNeighborhood (C.regularFixedNormalPair z).point_mem_neighborhood)).2

theorem nestedOuterPair_mdifferentiable :
    (nestedOuterPair Z C z).ambientChart.MDifferentiable 𝓘(ℂ, V.analyticModel)
      𝓘(ℂ, Z.regularAnalyticModel × (Fin p → ℂ)) := by
  rw [nestedOuterPair_chart]
  exact Z.regularFixedNormalPair_ambientChart_mdifferentiable _

theorem nestedOuterPair_analytic :
    ContMDiffOn 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, Z.regularAnalyticModel × (Fin p → ℂ)) ω
      (nestedOuterPair Z C z).ambientChart (nestedOuterPair Z C z).ambientChart.source := by
  rw [nestedOuterPair_chart]
  exact Immersion.IntersectionCoordinates.Constructions.regularFixedNormalPair_contMDiff Z _

theorem nestedOuterPair_symm_analytic :
    ContMDiffOn 𝓘(ℂ, Z.regularAnalyticModel × (Fin p → ℂ)) 𝓘(ℂ, V.analyticModel) ω
      (nestedOuterPair Z C z).ambientChart.symm (nestedOuterPair Z C z).ambientChart.target := by
  rw [nestedOuterPair_chart]
  exact Immersion.IntersectionCoordinates.Constructions.regularFixedNormalPair_symm_contMDiff Z _

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NestedNormalNeighborhood.Constructions
