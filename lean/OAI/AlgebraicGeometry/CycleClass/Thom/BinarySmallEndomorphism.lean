import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.BinarySmallRightCup
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.BinarySmallRelativeComparison

/-! # Binary Small Endomorphism -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.BinarySmallEndomorphism.Constructions

noncomputable section

/-! A cochain endomorphism compatible with both actual subspace restrictions acts on the binary-small relative cochain complex. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : TopCat.{0}) (A B : Set X)
  (f : AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X ⟶ AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X)

theorem endomorphism_restriction_zero (U : Set X)
    (hU : Geometric.LocalHomology.Cycles.subspaceChainInclusion X U ≫ Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B = 0)
    (fU : AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of U) ⟶
      AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of U))
    (hfU : AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X U ≫ fU =
      f ≫ AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X U)
    (n : ℕ) (c : (HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochains X A B).X n) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X U).f n
      (f.f n (HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B n c)) = 0 := by
  have h := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom hfU n)
    (HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B n c)
  change fU.f n ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X U).f n
    (HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B n c)) = _ at h
  rw [HodgeConjecture.DegreeTwo.BinarySmallRightCup.Constructions.binarySmallCochainInclusion_restriction X A B U hU, map_zero] at h
  exact h.symm

variable
  (fA : AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of A) ⟶ AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of A))
  (fB : AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of B) ⟶ AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of B))
  (hfA : AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X A ≫ fA =
    f ≫ AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X A)
  (hfB : AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X B ≫ fB =
    f ≫ AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X B)

def binaryEndomorphismFn (n : ℕ) (c : (HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochains X A B).X n) :
    (HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochains X A B).X n :=
  HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainLift X A B n (f.f n (HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B n c))
    (endomorphism_restriction_zero X A B f A
      (Geometric.HomologyWithSupports.Cycles.subspaceChainInclusion_binarySmallComplement_left X A B) fA hfA n c)
    (endomorphism_restriction_zero X A B f B
      (Geometric.HomologyWithSupports.Cycles.subspaceChainInclusion_binarySmallComplement_right X A B) fB hfB n c)

theorem binaryEndomorphismFn_inclusion (n : ℕ) (c : (HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochains X A B).X n) :
    HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B n (binaryEndomorphismFn X A B f fA fB hfA hfB n c) =
      f.f n (HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B n c) :=
  HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainLift_inclusion X A B n _ _ _

def binaryEndomorphism : HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochains X A B ⟶ HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochains X A B where
  f n := ModuleCat.ofHom {
    toFun := binaryEndomorphismFn X A B f fA fB hfA hfB n
    map_add' := by
      intro a b
      apply HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainInclusion_injective X A B n
      simp only [map_add, binaryEndomorphismFn_inclusion X A B f fA fB hfA hfB n]
    map_smul' := by
      intro r a
      apply HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainInclusion_injective X A B n
      simp only [map_smul, binaryEndomorphismFn_inclusion X A B f fA fB hfA hfB n,
        RingHom.id_apply] }
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainInclusion_injective X A B j
    change HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B j
      ((HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochains X A B).d i j (binaryEndomorphismFn X A B f fA fB hfA hfB i c)) =
        HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B j
          (binaryEndomorphismFn X A B f fA fB hfA hfB j ((HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochains X A B).d i j c))
    rw [HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainInclusion_d, binaryEndomorphismFn_inclusion,
      binaryEndomorphismFn_inclusion, HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainInclusion_d]
    exact ConcreteCategory.congr_hom (f.comm i j) _

theorem binaryEndomorphism_inclusion (n : ℕ) (c : (HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochains X A B).X n) :
    HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B n ((binaryEndomorphism X A B f fA fB hfA hfB).f n c) =
      f.f n (HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B n c) :=
  binaryEndomorphismFn_inclusion X A B f fA fB hfA hfB n c

end

end OAI.AlgebraicGeometry.CycleClass.Thom.BinarySmallEndomorphism.Constructions
