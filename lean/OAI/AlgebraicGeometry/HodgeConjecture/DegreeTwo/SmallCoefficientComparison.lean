import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RationalSmallDescent
import OAI.AlgebraicTopology.Duality.Poincare.LocallyFiniteRestrictionCoefficients
import OAI.AlgebraicTopology.Duality.Poincare.RelativeRationalEvaluationComparison

/-! # Small Coefficient Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmallCoefficientComparison.Constructions

noncomputable section

/-! Actual coefficient-change formulas for the small-support product calculation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

set_option backward.isDefEq.respectTransparency false

variable (X : TopCat.{0}) (A B : Set X) (n : ℕ)

theorem binaryRationalComplementProjection_integral (z : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n) :
    (RationalSmallDescent.Constructions.binaryRationalComplementProjection X A B).f n (AlgebraicTopology.Duality.Poincare.IntegralCapCoefficients.integralToScalarSingular (R := ℚ) X n z) =
      (1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ] ((CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B).f n z) := by
  rw [← AlgebraicTopology.Duality.Poincare.LocallyFiniteRestrictionCoefficients.rationalSingularChainsIso_one_tmul_eq_integralToScalar X n z]
  change (CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains.map (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B)).f n
    ((CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso X).inv.f n ((CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso X).hom.f n
      ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ] z))) = _
  have h := ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso X).hom_inv_id n)
    ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ] z)
  change (CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso X).inv.f n ((CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso X).hom.f n
    ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ] z)) = _ at h
  rw [h]
  rfl

theorem binaryRationalComplementHomologyIso_integral (hA : IsOpen A) (hB : IsOpen B)
    (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) n) :
    (RationalSmallDescent.Constructions.binaryRationalComplementHomologyIso X A B hA hB n).hom
      (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass _ n (AlgebraicTopology.Duality.Poincare.RationalizedChainClasses.Cycles.rationalizedChainCycle (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) n 1 z)) =
    (CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeHomologyIso X (A ∪ B) n).inv
      ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ]
        ((CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementHomologyIso X A B hA hB n).hom (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass _ n z))) := by
  apply (ModuleCat.mono_iff_injective (CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeHomologyIso X (A ∪ B) n).hom).mp
    inferInstance
  rw [Iso.inv_hom_id_apply]
  let w := AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative X A B) n z
  have hm : (RationalSmallDescent.Constructions.binaryRationalComplementHomologyIso X A B hA hB n).hom
      (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass _ n (AlgebraicTopology.Duality.Poincare.RationalizedChainClasses.Cycles.rationalizedChainCycle (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) n 1 z)) =
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass _ n (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeChainsIso X (A ∪ B)).hom n
      (AlgebraicTopology.Duality.Poincare.RationalizedChainClasses.Cycles.rationalizedChainCycle (CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X (A ∪ B)) n 1 w)) := by
    change HomologicalComplex.homologyMap
      (CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains.map (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative X A B) ≫
        (CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeChainsIso X (A ∪ B)).hom) n _ = _
    rw [HomologicalComplex.homologyMap_comp, ConcreteCategory.comp_apply,
      AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality, AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality]
    rfl
  rw [hm, AlgebraicTopology.Duality.Poincare.RelativeRationalEvaluationComparison.rationalRelativeHomologyIso_chainClass]
  congr 1
  exact (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative X A B) n z).symm

theorem binarySmallCup_scalarEvaluation (hA : IsOpen A) (hB : IsOpen B)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (A ∪ B) n)
    (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) n) :
    CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) X (A ∪ B) n c
      ((RationalSmallDescent.Constructions.binaryRationalComplementHomologyIso X A B hA hB n).hom
        (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass _ n (AlgebraicTopology.Duality.Poincare.RationalizedChainClasses.Cycles.rationalizedChainCycle (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) n 1 z))) =
    AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation X (A ∪ B) n c
      ((CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementHomologyIso X A B hA hB n).hom (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass _ n z)) := by
  rw [binaryRationalComplementHomologyIso_integral,
    AlgebraicTopology.Duality.Poincare.RelativeRationalEvaluationComparison.relativeRationalHomologyEvaluation_eq_scalarEvaluation]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmallCoefficientComparison.Constructions
