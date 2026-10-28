import OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.ImageImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.Normal.GysinRestriction

/-! # Divisor Gysin Thom -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.DivisorGysinThom.Constructions

noncomputable section

/-! At every regular point of an arbitrary source prime divisor,
its canonical Gysin class is the actual ambient-image Thom class on
the constructed neighborhood, with coefficient one. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions
  Gysin.Constructions GysinLocal.Constructions OuterPair.Constructions
  ImageImmersion.Constructions Scheme.PrimeParameter.Constructions.Class Normal.GysinRestriction.Constructions.ThomClass

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}
  [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
  [AlgebraicGeometry.IsNoetherian X.left]
  (i : X ⟶ Y) [IsClosedImmersion i.left]
  (z : {x : X.left // Order.coheight x = 1})
  (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom)
  (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Scheme.RegularSupport.Constructions.regularOver X (Purity.Constructions.primeSupport X z)))
  (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (Set.range (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularComplementInclusion)ᶜ) (2 * p))
  (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularThomClass)

local notation "P" => OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.OuterPair.Constructions.divisorOuterPair i z p hp x
local notation "hP" => OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.OuterPair.Constructions.divisorOuterPair_source_subset i z p hp x
local notation "C" => OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.ImageImmersion.Constructions.localDivisorImmersion i z p hp x P hP

theorem divisorGysinClass_localThom :
    eqToHom (congrArg (fun A => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (P).neighborhood) A (2 * (p + 1)))
      (Normal.GysinRestriction.Constructions.ThomClass.supportEquality (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) (Scheme.RegularSupport.Constructions.regularInclusion X (Purity.Constructions.primeSupport X z) x) P
        (Gysin.Constructions.divisorImageOpen i z) C (ImageImmersion.Constructions.localDivisorImmersion_range i z p hp x P hP)))
      (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
        (Gysin.Constructions.divisorImageOpen i z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (P).openNeighborhood (2 * (p + 1))
        (Gysin.Constructions.divisorGysinClass i z p hp a ha)) = (C).regularThomClass := by
  have hl := GysinLocal.Constructions.divisorGysinClass_restriction i z p hp x P hP a ha
  have ht := Normal.GysinRestriction.Constructions.ThomClass.localGysinIso_normalClass (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp)
    (Scheme.RegularSupport.Constructions.regularInclusion X (Purity.Constructions.primeSupport X z) x) P (Gysin.Constructions.divisorImageOpen i z)
    (Gysin.Constructions.divisorImage_supported i z p hp) (GysinLocal.Constructions.divisorParameter i z p hp x P hP)
    (GysinLocal.Constructions.divisorParameter_zero i z p hp x P hP) C (ImageImmersion.Constructions.localDivisorImmersion_range i z p hp x P hP)
    (OuterPair.Constructions.divisorOuterPair_mdifferentiable i z p hp x) (OuterPair.Constructions.divisorOuterPair_analytic i z p hp x)
    (OuterPair.Constructions.divisorOuterPair_symm_analytic i z p hp x)
    (Scheme.PrimeParameter.Constructions.Class.primeParameter_analytic X z x (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).closed.isEmbedding) hP)
    (fun y _ => Scheme.PrimeParameter.Constructions.Class.primeParameter_submersion X z x
      (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).closed.isEmbedding) hP y) a ha
  exact (congrArg (fun b => eqToHom (congrArg (fun A => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of (P).neighborhood) A (2 * (p + 1)))
    (Normal.GysinRestriction.Constructions.ThomClass.supportEquality (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) (Scheme.RegularSupport.Constructions.regularInclusion X (Purity.Constructions.primeSupport X z) x) P
      (Gysin.Constructions.divisorImageOpen i z) C (ImageImmersion.Constructions.localDivisorImmersion_range i z p hp x P hP))) b) hl).trans ht

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.DivisorGysinThom.Constructions
