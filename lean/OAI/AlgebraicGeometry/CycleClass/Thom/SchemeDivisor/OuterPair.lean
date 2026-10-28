import OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GysinLocal
import OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.SourceNeighborhood

/-! # Outer Pair -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.OuterPair.Constructions

noncomputable section

/-! Every regular source-prime point admits an actual outer normal
neighborhood whose source lies in the prime's regular ambient chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions
  Scheme.PrimeAmbientNormalPair.Constructions NormalPair.SourceNeighborhood.Constructions Immersion.IntersectionCoordinates.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}
  [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
  (i : X ⟶ Y) [IsClosedImmersion i.left]
  (z : {x : X.left // Order.coheight x = 1})
  (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom)
  (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Scheme.RegularSupport.Constructions.regularOver X (Purity.Constructions.primeSupport X z)))

def divisorOuterPair :
    ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularAnalyticModel (Fin p → ℂ)
      (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularComplementInclusion (Scheme.RegularSupport.Constructions.regularInclusion X (Purity.Constructions.primeSupport X z) x) :=
  Classical.choose (NormalPair.SourceNeighborhood.Constructions.exists_subpair_source_subset
    ((Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularFixedNormalPair (Scheme.RegularSupport.Constructions.regularInclusion X (Purity.Constructions.primeSupport X z) x))
    (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).closed.isEmbedding (Scheme.PrimeAmbientNormalPair.Constructions.primeAmbientPair X z x).openNeighborhood
    (Scheme.PrimeAmbientNormalPair.Constructions.primeAmbientPair X z x).point_mem_neighborhood)

theorem divisorOuterPair_chart : (divisorOuterPair i z p hp x).ambientChart =
    ((Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularFixedNormalPair (Scheme.RegularSupport.Constructions.regularInclusion X (Purity.Constructions.primeSupport X z) x)).ambientChart :=
  (Classical.choose_spec (NormalPair.SourceNeighborhood.Constructions.exists_subpair_source_subset
    ((Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularFixedNormalPair (Scheme.RegularSupport.Constructions.regularInclusion X (Purity.Constructions.primeSupport X z) x))
    (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).closed.isEmbedding (Scheme.PrimeAmbientNormalPair.Constructions.primeAmbientPair X z x).openNeighborhood
    (Scheme.PrimeAmbientNormalPair.Constructions.primeAmbientPair X z x).point_mem_neighborhood)).1

theorem divisorOuterPair_source_subset :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' (divisorOuterPair i z p hp x).neighborhood ⊆
      (Scheme.PrimeAmbientNormalPair.Constructions.primeAmbientPair X z x).neighborhood :=
  (Classical.choose_spec (NormalPair.SourceNeighborhood.Constructions.exists_subpair_source_subset
    ((Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularFixedNormalPair (Scheme.RegularSupport.Constructions.regularInclusion X (Purity.Constructions.primeSupport X z) x))
    (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).closed.isEmbedding (Scheme.PrimeAmbientNormalPair.Constructions.primeAmbientPair X z x).openNeighborhood
    (Scheme.PrimeAmbientNormalPair.Constructions.primeAmbientPair X z x).point_mem_neighborhood)).2

theorem divisorOuterPair_mdifferentiable :
    (divisorOuterPair i z p hp x).ambientChart.MDifferentiable
      𝓘(ℂ, (Scheme.ClosedImmersion.Constructions.schemeManifold Y).analyticModel)
      𝓘(ℂ, (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularAnalyticModel × (Fin p → ℂ)) := by
  rw [divisorOuterPair_chart]
  exact (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularFixedNormalPair_ambientChart_mdifferentiable _

theorem divisorOuterPair_analytic :
    ContMDiffOn 𝓘(ℂ, (Scheme.ClosedImmersion.Constructions.schemeManifold Y).analyticModel)
      𝓘(ℂ, (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularAnalyticModel × (Fin p → ℂ)) ω
      (divisorOuterPair i z p hp x).ambientChart (divisorOuterPair i z p hp x).ambientChart.source := by
  rw [divisorOuterPair_chart]
  exact Immersion.IntersectionCoordinates.Constructions.regularFixedNormalPair_contMDiff (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) _

theorem divisorOuterPair_symm_analytic :
    ContMDiffOn 𝓘(ℂ, (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularAnalyticModel × (Fin p → ℂ))
      𝓘(ℂ, (Scheme.ClosedImmersion.Constructions.schemeManifold Y).analyticModel) ω
      (divisorOuterPair i z p hp x).ambientChart.symm (divisorOuterPair i z p hp x).ambientChart.target := by
  rw [divisorOuterPair_chart]
  exact Immersion.IntersectionCoordinates.Constructions.regularFixedNormalPair_symm_contMDiff (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) _

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.OuterPair.Constructions
