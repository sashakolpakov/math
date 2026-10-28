import OAI.AlgebraicGeometry.CycleClass.Thom.TripleDiagonalCup
import OAI.AlgebraicGeometry.CycleClass.Thom.Relative.ExteriorAssociativity
import OAI.AlgebraicGeometry.CycleClass.Thom.ThomOpenRestriction

/-! # Supported Cup Degrees -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.SupportedCupDegrees.Constructions.TwoSupportAssociativity

/-! Associativity for three genuinely supported singular cup classes,
with the literal union of their complements and degree transport. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.CycleClass.Thom.TripleDiagonalCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Relative.ExteriorAssociativity.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Relative.ExteriorDegreeEvaluation.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossAssociateForward.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.TripleCross.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normal.Product.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.ThomOpenRestriction.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem twoSupportCohomologyCup_associative (X : TopCat) (A B C : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) (p q r : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B q)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X C r) :
    eqToHom (congrArg (fun d => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X ((A ∪ B) ∪ C) d)
      (Nat.add_assoc p q r))
      (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup X (A ∪ B) C (hA.union hB) hC (p + q) r
        (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup X A B hA hB p q a b) c) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 X) (TripleDiagonalCup.Constructions.unionAssociate_mapsTo X A B C) (p + (q + r))
      (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup X A (B ∪ C) hA (hB.union hC) p (q + r) a
        (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup X B C hB hC q r b c)) := by
  let AB := HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X X A B
  let BC := HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X X B C
  let left := HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup (TopCat.of (X × X)) X AB C
    ((hA.preimage continuous_fst).union (hB.preimage continuous_snd)) hC (p + q) r
    (HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X X A B hA hB p q a b) c
  let right := HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X (TopCat.of (X × X)) A BC hA
    ((hB.preimage continuous_fst).union (hC.preimage continuous_snd)) p (q + r) a
    (HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X X B C hB hC q r b c)
  have hleft := (Normal.Product.Constructions.Class.relativeCohomologyMap_degreeCast (TripleDiagonalCup.Constructions.leftTripleMap X) (TripleDiagonalCup.Constructions.leftTriple_mapsTo X A B C)
    (Nat.add_assoc p q r) left).symm.trans
    (congrArg (eqToHom (congrArg (fun d => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X ((A ∪ B) ∪ C) d)
      (Nat.add_assoc p q r))) (TripleDiagonalCup.Constructions.leftTriple_pullback X A B C hA hB hC p q r a b c))
  have hassoc := congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (TripleDiagonalCup.Constructions.leftTripleMap X)
    (TripleDiagonalCup.Constructions.leftTriple_mapsTo X A B C) (p + (q + r)))
    (Relative.ExteriorAssociativity.Constructions.relativeExteriorCup_associative X X X A B C hA hB hC p q r a b c)
  have hmaps :
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (TripleCross.Constructions.spaceAssociate ((X, X), X)).hom
          (Relative.CrossAssociateForward.Constructions.leftSupportMapsTo ((X, X), X) A B C) (p + (q + r)) ≫
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (TripleDiagonalCup.Constructions.leftTripleMap X) (TripleDiagonalCup.Constructions.leftTriple_mapsTo X A B C) (p + (q + r)) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (TripleDiagonalCup.Constructions.rightTripleMap X) (TripleDiagonalCup.Constructions.rightTriple_mapsTo X A B C) (p + (q + r)) ≫
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 X) (TripleDiagonalCup.Constructions.unionAssociate_mapsTo X A B C) (p + (q + r)) := by
    rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp, AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp]
    exact ThomOpenRestriction.Constructions.pairMap_congr ((TripleDiagonalCup.Constructions.tripleMap_associate X).trans (Category.id_comp (TripleDiagonalCup.Constructions.rightTripleMap X)).symm) _ _ (p + (q + r))
  have hright := (ConcreteCategory.congr_hom hmaps right).trans
    (congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 X)
      (TripleDiagonalCup.Constructions.unionAssociate_mapsTo X A B C) (p + (q + r))) (TripleDiagonalCup.Constructions.rightTriple_pullback X A B C hA hB hC p q r a b c))
  exact hleft.symm.trans (hassoc.trans hright)

end AlgebraicGeometry.CycleClass.Thom.SupportedCupDegrees.Constructions.TwoSupportAssociativity

namespace AlgebraicGeometry.CycleClass.Thom.SupportedCupDegrees.Constructions

/-! Explicit output degrees for the genuine supported cup, including
associativity with independent intermediate degree identifications. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.CycleClass.Thom.SupportedCupDegrees.Constructions.TwoSupportAssociativity OAI.AlgebraicGeometry.CycleClass.Thom.TripleDiagonalCup.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def cupAt (X : TopCat) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (p q n : ℕ) (h : p + q = n)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B q) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (A ∪ B) n :=
  eqToHom (congrArg (fun d => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (A ∪ B) d) h)
    (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup X A B hA hB p q a b)

theorem cupAt_associative (X : TopCat) (A B C : Set X) (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C)
    (p q r m l n : ℕ) (hm : p + q = m) (hl : q + r = l) (hn : p + l = n) (hmr : m + r = n)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B q)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X C r) :
    cupAt X (A ∪ B) C (hA.union hB) hC m r n hmr (cupAt X A B hA hB p q m hm a b) c =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 X) (TripleDiagonalCup.Constructions.unionAssociate_mapsTo X A B C) n
        (cupAt X A (B ∪ C) hA (hB.union hC) p l n hn a (cupAt X B C hB hC q r l hl b c)) := by
  cases hm
  cases hl
  cases hn
  exact TwoSupportAssociativity.twoSupportCohomologyCup_associative X A B C hA hB hC p q r a b c

theorem cupAt_cast_output (X : TopCat) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (p q n m : ℕ) (hn : p + q = n) (hm : n = m)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B q) :
    eqToHom (congrArg (fun d => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (A ∪ B) d) hm)
      (cupAt X A B hA hB p q n hn a b) = cupAt X A B hA hB p q m (hn.trans hm) a b := by
  cases hm
  rfl

end AlgebraicGeometry.CycleClass.Thom.SupportedCupDegrees.Constructions

end

end OAI
