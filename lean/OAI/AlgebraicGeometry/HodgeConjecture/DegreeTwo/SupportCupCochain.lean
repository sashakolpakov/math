import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.BinarySmallRelativeComparison
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportCup
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCup
import OAI.AlgebraicTopology.Products.CupCohomology

/-! # Support Cup Cochain -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportCupCochain.Constructions

noncomputable section

/-! A genuine cocycle representative for the previously defined two-support cup. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCup.Cycles OAI.AlgebraicTopology.Products.CupCohomology

set_option backward.isDefEq.respectTransparency false

variable (X : TopCat.{0}) (A B : Set X)

def twoSupportSmallCupCochain {p q : ℕ}
    (a : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
    (b : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B).X q) :
    (BinarySmallCochains.Constructions.binarySmallCochains X A B).X (p+q) :=
  BinarySmallCochains.Constructions.binarySmallCochainLift X A B (p+q)
    (AlgebraicTopology.Products.Cup.singularCup X ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p a)
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X B).f q b))
    (CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCupWith_restriction_zero X A
      (M := ModuleCat.of ℚ ℚ) (N := ModuleCat.of ℚ ℚ) (L := ModuleCat.of ℚ ℚ)
      (LinearMap.mul ℚ ℚ) (p := p) (q := q) a
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X B).f q b))
    (CycleClass.Geometric.RelativeCup.Cycles.absoluteRelativeCupWith_restriction_zero X B
      (M := ModuleCat.of ℚ ℚ) (N := ModuleCat.of ℚ ℚ) (L := ModuleCat.of ℚ ℚ)
      (LinearMap.mul ℚ ℚ) (p := p) (q := q)
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p a) b)

theorem twoSupportSmallCupCochain_inclusion {p q : ℕ}
    (a : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
    (b : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B).X q) :
    BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B (p+q) (twoSupportSmallCupCochain X A B a b) =
      AlgebraicTopology.Products.Cup.singularCup X ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p a)
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X B).f q b) :=
  BinarySmallCochains.Constructions.binarySmallCochainLift_inclusion X A B (p+q) _ _ _

theorem twoSupportSmallCupCochain_cocycle {p q : ℕ}
    (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p)
    (b : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B) q) :
    twoSupportSmallCupCochain X A B a.val b.val ∈ AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (BinarySmallCochains.Constructions.binarySmallCochains X A B) (p+q) := by
  rw [AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff]
  apply BinarySmallCochains.Constructions.binarySmallCochainInclusion_injective X A B (p+q+1)
  rw [map_zero, BinarySmallCochains.Constructions.binarySmallCochainInclusion_d, twoSupportSmallCupCochain_inclusion]
  let aa : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) p :=
    AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A) p a
  let bb : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) q :=
    AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X B) q b
  have h := AlgebraicTopology.Products.CupCohomology.cupWith_mem_cocycles (TopCat.toSSet.obj X)
    (M := ModuleCat.of ℚ ℚ) (N := ModuleCat.of ℚ ℚ) (L := ModuleCat.of ℚ ℚ)
    (LinearMap.mul ℚ ℚ) aa bb
  exact (AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) (p+q) _).mp h

def twoSupportSmallCupCocycle {p q : ℕ}
    (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p)
    (b : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B) q) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (BinarySmallCochains.Constructions.binarySmallCochains X A B) (p+q) :=
  ⟨twoSupportSmallCupCochain X A B a.val b.val,
    twoSupportSmallCupCochain_cocycle X A B a b⟩

theorem rationalSingularIntegralDualEquiv_scalar (n : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X n)
    (z : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n) :
    BinarySmallCochains.Constructions.rationalSingularIntegralDualEquiv X n c z =
      AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv (ModuleCat.of ℚ ℚ) X n c
        (AlgebraicTopology.Duality.Poincare.IntegralCapCoefficients.integralToScalarSingular (R := ℚ) X n z) := by
  let f : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n →ₗ[ℤ] ℚ :=
    ((AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv (ModuleCat.of ℚ ℚ) X n c).restrictScalars ℤ).comp
      (AlgebraicTopology.Duality.Poincare.IntegralCapCoefficients.integralToScalarSingular (R := ℚ) X n)
  have h : BinarySmallCochains.Constructions.rationalSingularIntegralDualEquiv X n c = f := by
    apply AlgebraicTopology.Cohomology.Singular.ChainDual.chainFunctional_ext (TopCat.toSSet.obj X) (ModuleCat.of ℤ ℚ)
    intro s
    change AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv (TopCat.toSSet.obj X) n c (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain _ s) =
      AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv (ModuleCat.of ℚ ℚ) X n c
        (AlgebraicTopology.Duality.Poincare.IntegralCapCoefficients.integralToScalarSimplicial (R := ℚ) (TopCat.toSSet.obj X) n (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain _ s))
    rw [AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv_simplex, AlgebraicTopology.Duality.Poincare.IntegralCapCoefficients.integralToScalarSimplicial_simplex]
    exact (AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv_simplex (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) c s).symm
  exact LinearMap.congr_fun h z

theorem twoSupportCohomologyCup_smallCochain_class (hA : IsOpen A) (hB : IsOpen B)
    {p q : ℕ}
    (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p)
    (b : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B) q) :
    HomologicalComplex.homologyMap (BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap X A B) (p+q)
      (SupportCup.Constructions.twoSupportCohomologyCup X A B hA hB p q (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ p a) (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ q b)) =
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (p+q) (twoSupportSmallCupCocycle X A B a b) := by
  apply (RationalDualComplex.Constructions.integralRationalDualUniversalCoefficientEquiv (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) (p+q)).injective
  ext w
  obtain ⟨w,rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) (p+q) w
  have : Epi ((CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B).f (p+q)) :=
    (IntegralSmallDescent.Constructions.integralChainDegree (p+q)).map_epi _
  obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective
    ((CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B).f (p+q))).mp inferInstance w.val
  have hzcycle : (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B).f (p+q) z ∈
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) (p+q) := hz.symm ▸ w.property
  have hw : w = ⟨(CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B).f (p+q) z,hzcycle⟩ := Subtype.ext hz.symm
  rw [hw, BinarySmallRelativeComparison.Constructions.binarySmallRelativeCohomologyMap_evaluation,
    RationalDualComplex.Constructions.integralRationalDualUniversalCoefficientEquiv_class_class]
  change AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation X (A ∪ B) (p+q) _
    ((CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementHomologyIso X A B hA hB (p+q)).hom _) = _
  rw [SupportCup.Constructions.twoSupportCup_small_projection_cup]
  have he := BinarySmallCochains.Constructions.binarySmallCochainInclusion_eval X A B (p+q)
    (twoSupportSmallCupCochain X A B a.val b.val) z
  rw [twoSupportSmallCupCochain_inclusion, rationalSingularIntegralDualEquiv_scalar] at he
  exact he

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportCupCochain.Constructions
