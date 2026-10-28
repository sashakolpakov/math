import OAI.AlgebraicGeometry.CycleClass.Thom.BinarySmallReversal
import OAI.AlgebraicGeometry.CycleClass.Thom.BinarySmallSwap
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportCupCochain
import OAI.AlgebraicTopology.Products.CupGradedCommutativity

/-! # Binary Small Cup Reversal -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.BinarySmallCupReversal.Constructions

/-! Signed reversal interchanges the actual two-support cup factors inside the binary-small cochain complex. -/

open _root_.CategoryTheory OAI.AlgebraicTopology.Products.CupGradedCommutativity
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportCupCochain.Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.BinarySmallReversal.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.BinarySmallSwap.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : TopCat.{0}) (A B : Set X)

def smallCocycleCast {m n : ℕ} (h : m = n) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochains X A B) m →ₗ[ℚ] AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochains X A B) n := by
  subst n
  exact LinearMap.id

theorem smallCocycleCast_val {m n : ℕ} (h : m = n)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochains X A B) m) :
    (smallCocycleCast X A B h c).val = HodgeConjecture.DegreeTwo.BinarySmallRightCup.Constructions.binarySmallCochainCast X A B h c.val := by
  subst n
  rfl

theorem smallCocycleCast_class {m n : ℕ} (h : m = n)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochains X A B) m) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ n (smallCocycleCast X A B h c) =
      eqToHom (congrArg (fun k => (HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochains X A B).homology k) h) (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ m c) := by
  subst n
  rfl

theorem binaryReversal_cup {p q : ℕ}
    (a : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
    (b : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B).X q) :
    (BinarySmallReversal.Constructions.binaryReversal X A B).f (p + q) (HodgeConjecture.DegreeTwo.SupportCupCochain.Constructions.twoSupportSmallCupCochain X A B a b) =
      (-1 : ℚ) ^ (p * q) • HodgeConjecture.DegreeTwo.BinarySmallRightCup.Constructions.binarySmallCochainCast X A B (Nat.add_comm q p)
        ((BinarySmallSwap.Constructions.binarySwap X A B).f (q + p)
          (HodgeConjecture.DegreeTwo.SupportCupCochain.Constructions.twoSupportSmallCupCochain X B A
            ((AlgebraicTopology.Products.RelativeReversal.relativeReversalCochainMap (ModuleCat.of ℚ ℚ) X B).f q b)
            ((AlgebraicTopology.Products.RelativeReversal.relativeReversalCochainMap (ModuleCat.of ℚ ℚ) X A).f p a))) := by
  apply HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainInclusion_injective X A B (p + q)
  rw [BinarySmallReversal.Constructions.binaryReversal_inclusion, HodgeConjecture.DegreeTwo.SupportCupCochain.Constructions.twoSupportSmallCupCochain_inclusion, map_smul,
    HodgeConjecture.DegreeTwo.BinarySmallRightCup.Constructions.binarySmallCochainCast_inclusion, BinarySmallSwap.Constructions.binarySwap_inclusion, HodgeConjecture.DegreeTwo.SupportCupCochain.Constructions.twoSupportSmallCupCochain_inclusion,
    AlgebraicTopology.Products.RelativeReversal.relativeReversalCochainMap_inclusion_apply, AlgebraicTopology.Products.RelativeReversal.relativeReversalCochainMap_inclusion_apply]
  exact AlgebraicTopology.Products.CupGradedCommutativity.singularReversalCochainMap_cup X _ _

theorem binaryReversal_cup_cocycle {p q : ℕ}
    (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p)
    (b : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B) q) :
    AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (BinarySmallReversal.Constructions.binaryReversal X A B) (p + q) (HodgeConjecture.DegreeTwo.SupportCupCochain.Constructions.twoSupportSmallCupCocycle X A B a b) =
      (-1 : ℚ) ^ (p * q) • smallCocycleCast X A B (Nat.add_comm q p)
        (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (BinarySmallSwap.Constructions.binarySwap X A B) (q + p)
          (HodgeConjecture.DegreeTwo.SupportCupCochain.Constructions.twoSupportSmallCupCocycle X B A
            (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (AlgebraicTopology.Products.RelativeReversal.relativeReversalCochainMap (ModuleCat.of ℚ ℚ) X B) q b)
            (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (AlgebraicTopology.Products.RelativeReversal.relativeReversalCochainMap (ModuleCat.of ℚ ℚ) X A) p a))) := by
  apply Subtype.ext
  simp only [Submodule.coe_smul]
  rw [AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap_val (BinarySmallReversal.Constructions.binaryReversal X A B), smallCocycleCast_val X A B]
  exact binaryReversal_cup X A B a.val b.val

end AlgebraicGeometry.CycleClass.Thom.BinarySmallCupReversal.Constructions

namespace AlgebraicGeometry.CycleClass.Thom.BinarySmallCupReversal.Constructions.TwoSupportCommutativity

/-! The actual two-support cohomology cup is graded commutative, with the support-swap and degree transports explicit. -/

open _root_.CategoryTheory OAI.AlgebraicTopology.Products.CupGradedCommutativity
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportCupCochain.Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.BinarySmallReversal.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.BinarySmallSwap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.BinarySmallCupReversal.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem homologyMap_degreeCast {C D : CochainComplex (ModuleCat.{0} ℚ) ℕ} (f : C ⟶ D)
    {m n : ℕ} (h : m = n) (c : C.homology m) :
    HomologicalComplex.homologyMap f n (eqToHom (congrArg (fun k => C.homology k) h) c) =
      eqToHom (congrArg (fun k => D.homology k) h) (HomologicalComplex.homologyMap f m c) := by
  subst n
  rfl

theorem twoSupportCup_graded_comm (X : TopCat.{0}) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B q) :
    HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup X A B hA hB p q a b =
      (-1 : ℚ) ^ (p * q) •
        eqToHom (congrArg (fun k => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (A ∪ B) k)
          (Nat.add_comm q p))
          (HomologicalComplex.homologyMap (BinarySmallSwap.Constructions.unionSwap X A B) (q + p)
            (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup X B A hB hA q p b a)) := by
  obtain ⟨a, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p a
  obtain ⟨b, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B) q b
  have h := congrArg (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochains X A B) (p + q))
    (binaryReversal_cup_cocycle X A B a b)
  rw [BinarySmallReversal.Constructions.binaryReversal_class X A B hA hB, map_smul, smallCocycleCast_class,
    ← AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, ← HodgeConjecture.DegreeTwo.SupportCupCochain.Constructions.twoSupportCohomologyCup_smallCochain_class X B A hB hA,
    AlgebraicTopology.Products.RelativeReversal.relativeReversalCochainMap_class, AlgebraicTopology.Products.RelativeReversal.relativeReversalCochainMap_class] at h
  apply (HodgeConjecture.DegreeTwo.BinarySmallRelativeComparison.Constructions.binarySmallRelativeCohomologyMap_bijective X A B hA hB (p + q)).injective
  rw [HodgeConjecture.DegreeTwo.SupportCupCochain.Constructions.twoSupportCohomologyCup_smallCochain_class, map_smul,
    homologyMap_degreeCast (HodgeConjecture.DegreeTwo.BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap X A B) (Nat.add_comm q p),
    ← BinarySmallSwap.Constructions.binarySwap_relative_cohomology]
  exact h

theorem twoSupportCup_even_comm (X : TopCat.{0}) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A (2 * p))
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B q) :
    HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup X A B hA hB (2 * p) q a b =
      eqToHom (congrArg (fun k => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (A ∪ B) k)
        (Nat.add_comm q (2 * p)))
        (HomologicalComplex.homologyMap (BinarySmallSwap.Constructions.unionSwap X A B) (q + 2 * p)
          (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup X B A hB hA q (2 * p) b a)) := by
  have h := twoSupportCup_graded_comm X A B hA hB (2 * p) q a b
  simpa only [pow_mul, neg_one_sq, one_pow, one_smul] using h

end AlgebraicGeometry.CycleClass.Thom.BinarySmallCupReversal.Constructions.TwoSupportCommutativity

end

end OAI
