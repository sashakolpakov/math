import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntegralSmallDescent
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RationalDualComplex

/-! # Binary Small Cochains -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions

noncomputable section

/-! Actual rational cochains on the integral quotient by both small supports. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

def rationalSingularIntegralDualEquiv (X : TopCat.{0}) (n : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X n ≃ₗ[ℚ]
      ((CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n →ₗ[ℤ] ℚ) where
  __ := AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv (TopCat.toSSet.obj X) n
  map_smul' r c := map_rat_smul (AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv (TopCat.toSSet.obj X) n) r c

abbrev binarySmallCochains (X : TopCat.{0}) (A B : Set X) :=
  RationalDualComplex.Constructions.integralRationalDualComplex (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B)

variable (X : TopCat.{0}) (A B : Set X)

def binarySmallCochainInclusion (n : ℕ) :
    (binarySmallCochains X A B).X n →ₗ[ℚ] (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X n where
  toFun c := (rationalSingularIntegralDualEquiv X n).symm
    (c.comp ((CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B).f n).hom)
  map_add' c d := by
    apply (rationalSingularIntegralDualEquiv X n).injective
    simp only [map_add, LinearEquiv.apply_symm_apply]
    rfl
  map_smul' r c := by
    apply (rationalSingularIntegralDualEquiv X n).injective
    simp only [map_smul, LinearEquiv.apply_symm_apply, RingHom.id_apply]
    rfl

theorem binarySmallCochainInclusion_eval (n : ℕ)
    (c : (binarySmallCochains X A B).X n) (z : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n) :
    rationalSingularIntegralDualEquiv X n (binarySmallCochainInclusion X A B n c) z =
      c ((CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B).f n z) := by
  change (rationalSingularIntegralDualEquiv X n)
    ((rationalSingularIntegralDualEquiv X n).symm _) z = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem binarySmallCochainInclusion_injective (n : ℕ) :
    Function.Injective (binarySmallCochainInclusion X A B n) := by
  intro c d h
  have : Epi ((CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B).f n) :=
    (IntegralSmallDescent.Constructions.integralChainDegree n).map_epi _
  apply LinearMap.ext
  intro w
  obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective
    ((CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B).f n)).mp inferInstance w
  exact (binarySmallCochainInclusion_eval X A B n c z).symm.trans
    ((congrArg (fun a => rationalSingularIntegralDualEquiv X n a z) h).trans
      (binarySmallCochainInclusion_eval X A B n d z))

theorem binarySmallCochainInclusion_d (i j : ℕ)
    (c : (binarySmallCochains X A B).X i) :
    binarySmallCochainInclusion X A B j ((binarySmallCochains X A B).d i j c) =
      (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d i j
        (binarySmallCochainInclusion X A B i c) := by
  apply (rationalSingularIntegralDualEquiv X j).injective
  ext z
  rw [binarySmallCochainInclusion_eval]
  change c ((CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B).d j i
    ((CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B).f j z)) =
    AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv (TopCat.toSSet.obj X) j
      ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d i j
        (binarySmallCochainInclusion X A B i c)) z
  rw [AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv_d]
  change _ = rationalSingularIntegralDualEquiv X i
    (binarySmallCochainInclusion X A B i c) ((CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d j i z)
  rw [binarySmallCochainInclusion_eval]
  exact congrArg c (ConcreteCategory.congr_hom
    ((CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B).comm j i) z)

theorem rationalSingularFunctional_restriction_zero (U : Set X) (n : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X n)
    (hc : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X U).f n c = 0) :
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X U).f n ≫
      ModuleCat.ofHom (rationalSingularIntegralDualEquiv X n c) = 0 := by
  apply ModuleCat.hom_ext
  have h := AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv_pullback
    (TopCat.toSSet.map (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U)) n c
  change AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv (TopCat.toSSet.obj (TopCat.of U)) n
    ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X U).f n c) = _ at h
  rw [hc, map_zero] at h
  exact h.symm

def binarySmallCochainLift (n : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X n)
    (hA : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X A).f n c = 0)
    (hB : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X B).f n c = 0) :
    (binarySmallCochains X A B).X n :=
  (IntegralSmallDescent.Constructions.binaryIntegralComplementDegreeDesc X A B n
    (ModuleCat.ofHom (rationalSingularIntegralDualEquiv X n c))
    (rationalSingularFunctional_restriction_zero X A n c hA)
    (rationalSingularFunctional_restriction_zero X B n c hB)).hom

theorem binarySmallCochainLift_inclusion (n : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X n)
    (hA : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X A).f n c = 0)
    (hB : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X B).f n c = 0) :
    binarySmallCochainInclusion X A B n (binarySmallCochainLift X A B n c hA hB) = c := by
  apply (rationalSingularIntegralDualEquiv X n).injective
  ext z
  rw [binarySmallCochainInclusion_eval]
  exact ConcreteCategory.congr_hom
    (IntegralSmallDescent.Constructions.binaryIntegralComplementDegreeDesc_projection X A B n
      (ModuleCat.ofHom (rationalSingularIntegralDualEquiv X n c))
      (rationalSingularFunctional_restriction_zero X A n c hA)
      (rationalSingularFunctional_restriction_zero X B n c hB)) z

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions
