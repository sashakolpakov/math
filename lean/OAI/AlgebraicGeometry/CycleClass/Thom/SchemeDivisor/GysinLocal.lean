import OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Gysin
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PrimeParameter

/-! # Gysin Local -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GysinLocal.Constructions

noncomputable section

/-! Near a regular source-prime point, the original global Gysin
pushforward of its canonical class is the local Gysin map of its
actual holomorphic normal equation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Module.Constructions
  Scheme.PrimeAmbientNormalPair.Constructions Scheme.PrimeParameter.Constructions.Class Gysin.Constructions
  Normal.GysinRestriction.Constructions Normal.GysinLocalIso.Constructions Normal.Product.Constructions.Class

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
  (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularAnalyticModel (Fin p → ℂ)
    (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularComplementInclusion (Scheme.RegularSupport.Constructions.regularInclusion X (Purity.Constructions.primeSupport X z) x))
  (hP : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' P.neighborhood ⊆ (Scheme.PrimeAmbientNormalPair.Constructions.primeAmbientPair X z x).neighborhood)

abbrev divisorParameter := Scheme.PrimeParameter.Constructions.Class.primeParameter X z x
  (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).closed.isEmbedding) hP

theorem divisorParameter_zero (y : HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).closed.isEmbedding) :
    divisorParameter i z p hp x P hP y = 0 ↔
      (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularComplementInclusion y.val ∉ Gysin.Constructions.divisorImageOpen i z :=
  (Scheme.PrimeParameter.Constructions.Class.primeParameter_zero_iff X z x _ hP y).trans (Gysin.Constructions.divisorImage_mem_iff i z y.val).symm

variable [AlgebraicGeometry.IsNoetherian X.left]

theorem divisorSourceRestriction_normal :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
        (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).closed.isEmbedding : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
      (Normal.GysinRestriction.Constructions.sourceMapsTo (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) (Gysin.Constructions.divisorImageOpen i z)
        (Scheme.RegularSupport.Constructions.regularInclusion X (Purity.Constructions.primeSupport X z) x) P (divisorParameter i z p hp x P hP)
        (divisorParameter_zero i z p hp x P hP)) 2
      ((AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (Gysin.Constructions.divisorSourceComplement i z) 2).inv
        (Module.Constructions.supportedDivisorClass X z)) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (divisorParameter i z p hp x P hP)
      (A := divisorParameter i z p hp x P hP ⁻¹' {0}ᶜ) (B := {0}ᶜ) (fun _ hy => hy) 2
      (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1) := by
  have hc := Normal.Product.Constructions.Class.relativeCohomologyMap_targetCast
    (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).closed.isEmbedding : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
    (Gysin.Constructions.divisorSourceComplement i z).symm
    (Scheme.PrimeParameter.Constructions.Class.primeParameter_mapsTo X z x _ hP)
    (Normal.GysinRestriction.Constructions.sourceMapsTo (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) (Gysin.Constructions.divisorImageOpen i z)
      (Scheme.RegularSupport.Constructions.regularInclusion X (Purity.Constructions.primeSupport X z) x) P (divisorParameter i z p hp x P hP)
      (divisorParameter_zero i z p hp x P hP)) 2 (Module.Constructions.supportedDivisorClass X z)
  exact hc.trans (Scheme.PrimeParameter.Constructions.Class.supportedDivisorClass_parameter X z x _ hP)

variable
  (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (Set.range (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularComplementInclusion)ᶜ) (2 * p))
  (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularThomClass)

theorem divisorGysinClass_restriction :
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
      (Gysin.Constructions.divisorImageOpen i z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) P.openNeighborhood (2 * (p + 1))
      (Gysin.Constructions.divisorGysinClass i z p hp a ha) =
    (Normal.GysinLocalIso.Constructions.localGysinIso (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) (Scheme.RegularSupport.Constructions.regularInclusion X (Purity.Constructions.primeSupport X z) x) P
      (Gysin.Constructions.divisorImageOpen i z) (Gysin.Constructions.divisorImage_supported i z p hp) (divisorParameter i z p hp x P hP)
      (divisorParameter_zero i z p hp x P hP) a ha).hom
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (divisorParameter i z p hp x P hP)
        (A := divisorParameter i z p hp x P hP ⁻¹' {0}ᶜ) (B := {0}ᶜ) (fun _ hy => hy) 2
        (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1)) := by
  have h := ConcreteCategory.congr_hom
    (Normal.GysinRestriction.Constructions.globalGysinIso_restriction (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) (Gysin.Constructions.divisorImageOpen i z)
      (Gysin.Constructions.divisorImage_supported i z p hp) a ha (Scheme.RegularSupport.Constructions.regularInclusion X (Purity.Constructions.primeSupport X z) x) P
      (divisorParameter i z p hp x P hP) (divisorParameter_zero i z p hp x P hP))
    ((AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (Gysin.Constructions.divisorSourceComplement i z) 2).inv
      (Module.Constructions.supportedDivisorClass X z))
  exact h.symm.trans (congrArg
    (fun b => (Normal.GysinLocalIso.Constructions.localGysinIso (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) (Scheme.RegularSupport.Constructions.regularInclusion X (Purity.Constructions.primeSupport X z) x) P
      (Gysin.Constructions.divisorImageOpen i z) (Gysin.Constructions.divisorImage_supported i z p hp) (divisorParameter i z p hp x P hP)
      (divisorParameter_zero i z p hp x P hP) a ha).hom b)
    (divisorSourceRestriction_normal i z p hp x P hP))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GysinLocal.Constructions
