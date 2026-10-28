import OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.DivisorGysinThom
import OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.CommonNeighborhood

/-! # Gysin Small -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GysinSmall.Constructions

noncomputable section

/-! The actual Gysin class of an arbitrary prime divisor has a coefficient-one image Thom presentation on a constructed normal neighborhood inside any prescribed ambient open around a regular divisor point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Gysin.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GysinLocal.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.ImageImmersion.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PrimeAmbientNormalPair.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PrimeParameter.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Normal.GysinRestriction.Constructions.ThomClass
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.CommonNeighborhood.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.IntersectionCoordinates.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}
  [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
  [AlgebraicGeometry.IsNoetherian X.left]
  (i : X ⟶ Y) [IsClosedImmersion i.left] (z : {x : X.left // Order.coheight x = 1})
  (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom)
  (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Scheme.RegularSupport.Constructions.regularOver X (Purity.Constructions.primeSupport X z)))
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
  (hxU : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i (Scheme.RegularSupport.Constructions.regularInclusion X (Purity.Constructions.primeSupport X z) x) ∈ U)
  (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (Set.range (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularComplementInclusion)ᶜ) (2 * p))
  (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularThomClass)

include hxU in
theorem exists_small_divisorGysin_Thom :
    ∃ P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularAnalyticModel (Fin p → ℂ)
      (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularComplementInclusion (Scheme.RegularSupport.Constructions.regularInclusion X (Purity.Constructions.primeSupport X z) x),
    ∃ hP : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' P.neighborhood ⊆ (Scheme.PrimeAmbientNormalPair.Constructions.primeAmbientPair X z x).neighborhood,
      P.neighborhood ⊆ U ∧
      eqToHom (congrArg (fun A => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of P.neighborhood) A (2 * (p + 1)))
        (Normal.GysinRestriction.Constructions.ThomClass.supportEquality (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) (Scheme.RegularSupport.Constructions.regularInclusion X (Purity.Constructions.primeSupport X z) x) P
          (Gysin.Constructions.divisorImageOpen i z) (ImageImmersion.Constructions.localDivisorImmersion i z p hp x P hP)
          (ImageImmersion.Constructions.localDivisorImmersion_range i z p hp x P hP)))
        (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
          (Gysin.Constructions.divisorImageOpen i z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) P.openNeighborhood (2 * (p + 1))
          (Gysin.Constructions.divisorGysinClass i z p hp a ha)) = (ImageImmersion.Constructions.localDivisorImmersion i z p hp x P hP).regularThomClass := by
  obtain ⟨P, hchart, hP, hPU⟩ := NormalPair.CommonNeighborhood.Constructions.exists_subpair_source_ambient
    ((Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularFixedNormalPair (Scheme.RegularSupport.Constructions.regularInclusion X (Purity.Constructions.primeSupport X z) x))
    (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).closed.isEmbedding (Scheme.PrimeAmbientNormalPair.Constructions.primeAmbientPair X z x).openNeighborhood
    (Scheme.PrimeAmbientNormalPair.Constructions.primeAmbientPair X z x).point_mem_neighborhood U hxU
  refine ⟨P, hP, hPU, ?_⟩
  have hPd : P.ambientChart.MDifferentiable
      𝓘(ℂ, (Scheme.ClosedImmersion.Constructions.schemeManifold Y).analyticModel)
      𝓘(ℂ, (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularAnalyticModel × (Fin p → ℂ)) := by
    rw [hchart]
    exact (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularFixedNormalPair_ambientChart_mdifferentiable _
  have hPa : ContMDiffOn 𝓘(ℂ, (Scheme.ClosedImmersion.Constructions.schemeManifold Y).analyticModel)
      𝓘(ℂ, (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularAnalyticModel × (Fin p → ℂ)) ω
      P.ambientChart P.ambientChart.source := by
    rw [hchart]
    exact Immersion.IntersectionCoordinates.Constructions.regularFixedNormalPair_contMDiff (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) _
  have hPi : ContMDiffOn 𝓘(ℂ, (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularAnalyticModel × (Fin p → ℂ))
      𝓘(ℂ, (Scheme.ClosedImmersion.Constructions.schemeManifold Y).analyticModel) ω P.ambientChart.symm P.ambientChart.target := by
    rw [hchart]
    exact Immersion.IntersectionCoordinates.Constructions.regularFixedNormalPair_symm_contMDiff (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) _
  have hl := GysinLocal.Constructions.divisorGysinClass_restriction i z p hp x P hP a ha
  have ht := Normal.GysinRestriction.Constructions.ThomClass.localGysinIso_normalClass (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp)
    (Scheme.RegularSupport.Constructions.regularInclusion X (Purity.Constructions.primeSupport X z) x) P (Gysin.Constructions.divisorImageOpen i z)
    (Gysin.Constructions.divisorImage_supported i z p hp) (GysinLocal.Constructions.divisorParameter i z p hp x P hP)
    (GysinLocal.Constructions.divisorParameter_zero i z p hp x P hP) (ImageImmersion.Constructions.localDivisorImmersion i z p hp x P hP)
    (ImageImmersion.Constructions.localDivisorImmersion_range i z p hp x P hP) hPd hPa hPi
    (Scheme.PrimeParameter.Constructions.Class.primeParameter_analytic X z x (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).closed.isEmbedding) hP)
    (fun y _ => Scheme.PrimeParameter.Constructions.Class.primeParameter_submersion X z x
      (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).closed.isEmbedding) hP y) a ha
  exact (congrArg (fun b => eqToHom (congrArg (fun A => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of P.neighborhood) A (2 * (p + 1)))
    (Normal.GysinRestriction.Constructions.ThomClass.supportEquality (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) (Scheme.RegularSupport.Constructions.regularInclusion X (Purity.Constructions.primeSupport X z) x) P
      (Gysin.Constructions.divisorImageOpen i z) (ImageImmersion.Constructions.localDivisorImmersion i z p hp x P hP)
      (ImageImmersion.Constructions.localDivisorImmersion_range i z p hp x P hP))) b) hl).trans ht

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GysinSmall.Constructions
