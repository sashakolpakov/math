import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportCupCochain
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.BinarySmallRightCup

/-! # Support Cup Differential -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportCupDifferential.Constructions

noncomputable section

/-! The actual two-support cup obeys the cochain Leibniz identity before passing to cohomology. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false

variable (X : TopCat.{0}) (A B : Set X)

theorem relativeCochainInclusion_d_apply (S : Set X) (p q : ℕ)
    (a : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X S).X p) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X S).f q
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X S).d p q a) =
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d p q
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X S).f p a) :=
  (ConcreteCategory.congr_hom ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X S).comm p q) a).symm

theorem twoSupportSmallCupCochain_zero_left (p q : ℕ)
    (b : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B).X q) :
    SupportCupCochain.Constructions.twoSupportSmallCupCochain X A B (p := p) 0 b = 0 := by
  apply BinarySmallCochains.Constructions.binarySmallCochainInclusion_injective X A B (p+q)
  rw [map_zero, SupportCupCochain.Constructions.twoSupportSmallCupCochain_inclusion, map_zero]
  exact AlgebraicTopology.Products.Cup.cupWith_zero_left (TopCat.toSSet.obj X)
    (M := ModuleCat.of ℚ ℚ) (N := ModuleCat.of ℚ ℚ) (L := ModuleCat.of ℚ ℚ)
    (LinearMap.mul ℚ ℚ) (p := p) _

theorem twoSupportSmallCupCochain_zero_right (p q : ℕ)
    (a : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p) :
    SupportCupCochain.Constructions.twoSupportSmallCupCochain X A B (q := q) a 0 = 0 := by
  apply BinarySmallCochains.Constructions.binarySmallCochainInclusion_injective X A B (p+q)
  rw [map_zero, SupportCupCochain.Constructions.twoSupportSmallCupCochain_inclusion, map_zero]
  exact AlgebraicTopology.Products.Cup.cupWith_zero_right (TopCat.toSSet.obj X)
    (M := ModuleCat.of ℚ ℚ) (N := ModuleCat.of ℚ ℚ) (L := ModuleCat.of ℚ ℚ)
    (LinearMap.mul ℚ ℚ) (q := q) _

theorem twoSupportSmallCupCochain_coboundary (p q : ℕ)
    (a : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
    (b : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B).X q) :
    (BinarySmallCochains.Constructions.binarySmallCochains X A B).d (p+q) (p+q+1) (SupportCupCochain.Constructions.twoSupportSmallCupCochain X A B a b) =
    BinarySmallRightCup.Constructions.binarySmallCochainCast X A B (by omega : (p+1)+q=p+q+1)
      (SupportCupCochain.Constructions.twoSupportSmallCupCochain X A B
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).d p (p+1) a) b) +
    (-1 : ℤ)^p • SupportCupCochain.Constructions.twoSupportSmallCupCochain X A B a
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B).d q (q+1) b) := by
  apply BinarySmallCochains.Constructions.binarySmallCochainInclusion_injective X A B (p+q+1)
  rw [map_add, map_zsmul, BinarySmallCochains.Constructions.binarySmallCochainInclusion_d, BinarySmallRightCup.Constructions.binarySmallCochainCast_inclusion,
    SupportCupCochain.Constructions.twoSupportSmallCupCochain_inclusion, SupportCupCochain.Constructions.twoSupportSmallCupCochain_inclusion]
  have hr : BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B (p+q+1)
      (SupportCupCochain.Constructions.twoSupportSmallCupCochain X A B (p := p) (q := q+1) a
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B).d q (q+1) b)) =
      AlgebraicTopology.Products.Cup.singularCup X ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p a)
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X B).f (q+1)
          ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B).d q (q+1) b)) :=
    SupportCupCochain.Constructions.twoSupportSmallCupCochain_inclusion X A B (p := p) (q := q+1) a
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B).d q (q+1) b)
  rw [hr, relativeCochainInclusion_d_apply, relativeCochainInclusion_d_apply]
  exact AlgebraicTopology.Products.Cup.cupWith_coboundary (TopCat.toSSet.obj X)
    (M := ModuleCat.of ℚ ℚ) (N := ModuleCat.of ℚ ℚ) (L := ModuleCat.of ℚ ℚ)
    (LinearMap.mul ℚ ℚ)
    ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p a)
    ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X B).f q b)

theorem twoSupportSmallCupCochain_primitive_left (p q : ℕ)
    (a : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
    (b : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B) q) :
    (BinarySmallCochains.Constructions.binarySmallCochains X A B).d (p+q) (p+q+1) (SupportCupCochain.Constructions.twoSupportSmallCupCochain X A B a b.val) =
    BinarySmallRightCup.Constructions.binarySmallCochainCast X A B (by omega : (p+1)+q=p+q+1)
      (SupportCupCochain.Constructions.twoSupportSmallCupCochain X A B
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).d p (p+1) a) b.val) := by
  rw [twoSupportSmallCupCochain_coboundary, AlgebraicTopology.Cohomology.Singular.Evaluation.cochainCocycle_d_eq_zero _ _ _ b,
    twoSupportSmallCupCochain_zero_right, smul_zero, add_zero]

theorem twoSupportSmallCupCochain_primitive_right (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p)
    (b : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B).X q) :
    (BinarySmallCochains.Constructions.binarySmallCochains X A B).d (p+q) (p+q+1)
      ((-1 : ℤ)^p • SupportCupCochain.Constructions.twoSupportSmallCupCochain X A B a.val b) =
    SupportCupCochain.Constructions.twoSupportSmallCupCochain X A B a.val
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B).d q (q+1) b) := by
  rw [map_zsmul, twoSupportSmallCupCochain_coboundary, AlgebraicTopology.Cohomology.Singular.Evaluation.cochainCocycle_d_eq_zero _ _ _ a,
    twoSupportSmallCupCochain_zero_left, map_zero, zero_add, smul_smul, ← mul_pow]
  simp

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportCupDifferential.Constructions
