import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.BinarySmallRightCup
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportCupCochain

/-! # Support Cup Associativity -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportCupAssociativity.Constructions

noncomputable section

/-! Associativity of the actual two-support cup with an ordinary right factor. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false

variable (X : TopCat.{0}) (A B : Set X)

def binarySmallCocycleCast {m n : ℕ} (h : m=n) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (BinarySmallCochains.Constructions.binarySmallCochains X A B) m →ₗ[ℚ]
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (BinarySmallCochains.Constructions.binarySmallCochains X A B) n := by
  subst n
  exact LinearMap.id

def binarySmallCohomologyCast {m n : ℕ} (h : m=n) :
    (BinarySmallCochains.Constructions.binarySmallCochains X A B).homology m →ₗ[ℚ]
      (BinarySmallCochains.Constructions.binarySmallCochains X A B).homology n := by
  subst n
  exact LinearMap.id

theorem binarySmallCocycleCast_val {m n : ℕ} (h : m=n)
    (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (BinarySmallCochains.Constructions.binarySmallCochains X A B) m) :
    (binarySmallCocycleCast X A B h a).val = BinarySmallRightCup.Constructions.binarySmallCochainCast X A B h a.val := by
  subst n
  rfl

theorem binarySmallCohomologyCast_class {m n : ℕ} (h : m=n)
    (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (BinarySmallCochains.Constructions.binarySmallCochains X A B) m) :
    binarySmallCohomologyCast X A B h (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ m a) =
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ n (binarySmallCocycleCast X A B h a) := by
  subst n
  rfl

theorem binarySmallRelativeCohomologyMap_degreeCast {m n : ℕ} (h : m=n)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (A ∪ B) m) :
    HomologicalComplex.homologyMap (BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap X A B) n
      (CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeCohomologyCast (ModuleCat.of ℚ ℚ) X (A ∪ B) h a) =
    binarySmallCohomologyCast X A B h
      (HomologicalComplex.homologyMap (BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap X A B) m a) := by
  subst n
  rfl

theorem binarySmallRelativeCochainMap_rightCup (p q : ℕ)
    (a : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (A ∪ B)).X p)
    (b : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X q) :
    (BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap X A B).f (p+q)
      (CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup X (A ∪ B) p q a b) =
    BinarySmallRightCup.Constructions.binarySmallRightCup X A B p q ((BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap X A B).f p a) b := by
  apply BinarySmallCochains.Constructions.binarySmallCochainInclusion_injective X A B (p+q)
  rw [BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap_inclusion, BinarySmallRightCup.Constructions.binarySmallRightCup_inclusion,
    BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap_inclusion]
  exact CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCupWith_inclusion X (A ∪ B)
    (M := ModuleCat.of ℚ ℚ) (N := ModuleCat.of ℚ ℚ) (L := ModuleCat.of ℚ ℚ)
    (LinearMap.mul ℚ ℚ) a b

theorem binarySmallRelativeCohomologyMap_rightCup (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (A ∪ B) p)
    (b : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) q) :
    HomologicalComplex.homologyMap (BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap X A B) (p+q)
      (CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup (R := ℚ) X (A ∪ B) p q a (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) q b)) =
      BinarySmallRightCup.Constructions.binarySmallRightCupClass X A B p q b
        (HomologicalComplex.homologyMap (BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap X A B) p a) := by
  obtain ⟨a,rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (A ∪ B)) p a
  rw [CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup_class_class, AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality,
    AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, BinarySmallRightCup.Constructions.binarySmallRightCupClass_class]
  apply congrArg (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (BinarySmallCochains.Constructions.binarySmallCochains X A B) (p+q))
  apply Subtype.ext
  exact binarySmallRelativeCochainMap_rightCup X A B p q a.val b.val

theorem twoSupportSmallCupCochain_assoc {p q r : ℕ}
    (a : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
    (b : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B).X q)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X r) :
    BinarySmallRightCup.Constructions.binarySmallCochainCast X A B (Nat.add_assoc p q r)
      (BinarySmallRightCup.Constructions.binarySmallRightCup X A B (p+q) r (SupportCupCochain.Constructions.twoSupportSmallCupCochain X A B a b) c) =
      SupportCupCochain.Constructions.twoSupportSmallCupCochain X A B a (CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup X B q r b c) := by
  apply BinarySmallCochains.Constructions.binarySmallCochainInclusion_injective X A B (p+(q+r))
  rw [BinarySmallRightCup.Constructions.binarySmallCochainCast_inclusion, BinarySmallRightCup.Constructions.binarySmallRightCup_inclusion,
    SupportCupCochain.Constructions.twoSupportSmallCupCochain_inclusion, SupportCupCochain.Constructions.twoSupportSmallCupCochain_inclusion]
  simp only [CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup, CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCupWith_inclusion]
  exact AlgebraicTopology.Products.Cup.cup_assoc (TopCat.toSSet.obj X)
    ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p a)
    ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X B).f q b) c

theorem twoSupportCohomologyCup_right_assoc (hA : IsOpen A) (hB : IsOpen B)
    {p q r : ℕ}
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B q)
    (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X r) :
    CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeCohomologyCast (ModuleCat.of ℚ ℚ) X (A ∪ B) (Nat.add_assoc p q r)
      (CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup (R := ℚ) X (A ∪ B) (p+q) r
        (SupportCup.Constructions.twoSupportCohomologyCup X A B hA hB p q a b) c) =
      SupportCup.Constructions.twoSupportCohomologyCup X A B hA hB p (q+r) a
        (CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup (R := ℚ) X B q r b c) := by
  obtain ⟨a,rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p a
  obtain ⟨b,rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B) q b
  obtain ⟨c,rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) r c
  apply (BinarySmallRelativeComparison.Constructions.binarySmallRelativeCohomologyMap_bijective X A B hA hB (p+(q+r))).injective
  rw [binarySmallRelativeCohomologyMap_degreeCast,
    binarySmallRelativeCohomologyMap_rightCup, SupportCupCochain.Constructions.twoSupportCohomologyCup_smallCochain_class,
    BinarySmallRightCup.Constructions.binarySmallRightCupClass_class, binarySmallCohomologyCast_class,
    CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup_class_class, SupportCupCochain.Constructions.twoSupportCohomologyCup_smallCochain_class]
  apply congrArg (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (BinarySmallCochains.Constructions.binarySmallCochains X A B) (p+(q+r)))
  apply Subtype.ext
  rw [binarySmallCocycleCast_val]
  exact twoSupportSmallCupCochain_assoc X A B a.val b.val c.val

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportCupAssociativity.Constructions
