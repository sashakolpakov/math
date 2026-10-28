import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularDivisorImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.NormalPairAnalytic
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.IntersectionCoordinates

/-! # Prime Ambient Normal Pair -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PrimeAmbientNormalPair.Constructions

noncomputable section

/-! Every regular point of an arbitrary prime divisor has a native
holomorphic ambient normal pair which avoids the actual singular
boundary and defines the full divisor support on its neighborhood. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularDivisorImmersion.Constructions
  Open.NormalNeighborhoodInverse.Constructions.PairTransport Open.NormalPairAnalytic.Constructions.Differentiable Open.NormalPairAnalytic.Constructions
  Immersion.IntersectionCoordinates.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] (z : {x : X.left // Order.coheight x = 1})
  (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (RegularSupport.Constructions.regularOver X (SchemeDivisor.Purity.Constructions.primeSupport X z)))

abbrev primeAmbientPair : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (RegularSupport.Constructions.regularModel X (SchemeDivisor.Purity.Constructions.primeSupport X z)) (Fin 1 → ℂ)
    (RegularSupport.Constructions.regularInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z)) x :=
  Open.NormalNeighborhoodInverse.Constructions.PairTransport.openTransportNormalPair ((RegularDivisorImmersion.Constructions.regularPrimeImmersion X z).regularFixedNormalPair x)
    Subtype.val (RegularSupport.Constructions.regularAmbientOpen X (SchemeDivisor.Purity.Constructions.primeSupport X z)).isOpenEmbedding'

theorem primeAmbientPair_mdifferentiable :
    (primeAmbientPair X z x).ambientChart.MDifferentiable
      𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
      𝓘(ℂ, RegularSupport.Constructions.regularModel X (SchemeDivisor.Purity.Constructions.primeSupport X z) × (Fin 1 → ℂ)) :=
  Open.NormalPairAnalytic.Constructions.Differentiable.openTransportNormalPair_mdifferentiable (RegularSupport.Constructions.regularAmbientOpen X (SchemeDivisor.Purity.Constructions.primeSupport X z))
    ((RegularDivisorImmersion.Constructions.regularPrimeImmersion X z).regularFixedNormalPair x)
    ((RegularDivisorImmersion.Constructions.regularPrimeImmersion X z).regularFixedNormalPair_ambientChart_mdifferentiable x)

theorem primeAmbientPair_analytic :
    ContMDiffOn 𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
      𝓘(ℂ, RegularSupport.Constructions.regularModel X (SchemeDivisor.Purity.Constructions.primeSupport X z) × (Fin 1 → ℂ)) ω
      (primeAmbientPair X z x).ambientChart (primeAmbientPair X z x).ambientChart.source :=
  Open.NormalPairAnalytic.Constructions.openTransportNormalPair_analytic (RegularSupport.Constructions.regularAmbientOpen X (SchemeDivisor.Purity.Constructions.primeSupport X z))
    ((RegularDivisorImmersion.Constructions.regularPrimeImmersion X z).regularFixedNormalPair x)
    (Immersion.IntersectionCoordinates.Constructions.regularFixedNormalPair_contMDiff (RegularDivisorImmersion.Constructions.regularPrimeImmersion X z) x)

theorem primeAmbientPair_symm_analytic :
    ContMDiffOn 𝓘(ℂ, RegularSupport.Constructions.regularModel X (SchemeDivisor.Purity.Constructions.primeSupport X z) × (Fin 1 → ℂ))
      𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) ω
      (primeAmbientPair X z x).ambientChart.symm (primeAmbientPair X z x).ambientChart.target :=
  Open.NormalPairAnalytic.Constructions.openTransportNormalPair_symm_analytic (RegularSupport.Constructions.regularAmbientOpen X (SchemeDivisor.Purity.Constructions.primeSupport X z))
    ((RegularDivisorImmersion.Constructions.regularPrimeImmersion X z).regularFixedNormalPair x)
    (Immersion.IntersectionCoordinates.Constructions.regularFixedNormalPair_symm_contMDiff (RegularDivisorImmersion.Constructions.regularPrimeImmersion X z) x)

theorem primeAmbientPair_avoids_boundary :
    (primeAmbientPair X z x).neighborhood ⊆ RegularSupport.Constructions.regularAmbientOpen X (SchemeDivisor.Purity.Constructions.primeSupport X z) := by
  intro y hy
  rw [Open.NormalNeighborhoodInverse.Constructions.PairTransport.openTransportNormalPair_neighborhood] at hy
  obtain ⟨w, _, rfl⟩ := hy
  exact w.property

theorem primeAmbientPair_zero_iff (y : (primeAmbientPair X z x).neighborhood) :
    (primeAmbientPair X z x).normalCoordinate y = 0 ↔
      y.val ∈ Set.range (RegularSupport.Constructions.supportInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z)) := by
  refine ((primeAmbientPair X z x).mem_range_iff y).symm.trans ?_
  constructor
  · intro hy
    exact RegularSupport.Constructions.regularInclusion_subset X (SchemeDivisor.Purity.Constructions.primeSupport X z) hy
  · intro hy
    by_contra hn
    have hb : y.val ∈ RegularSupport.Constructions.analyticBoundary X (SchemeDivisor.Purity.Constructions.primeSupport X z) := by
      rw [RegularSupport.Constructions.analyticBoundary_eq]
      exact ⟨hy, hn⟩
    exact primeAmbientPair_avoids_boundary X z x y.property hb

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PrimeAmbientNormalPair.Constructions
