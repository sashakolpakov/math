import OAI.AlgebraicGeometry.CycleClass.Thom.Relative.TripleCrossSpanning
import OAI.AlgebraicGeometry.CycleClass.Thom.Relative.ExteriorDegreeEvaluation

/-! # Exterior Associativity -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Relative.ExteriorAssociativity.Constructions

noncomputable section

/-! Associativity of the actual relative exterior cup under the genuine
product reassociation, with explicit cohomological degree transport. -/

open _root_.CategoryTheory _root_.HomologicalComplex

open OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossAssociateForward.Constructions.HomologyAssociativity OAI.AlgebraicGeometry.CycleClass.Thom.Relative.ExteriorDegreeEvaluation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossAssociateForward.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Relative.ExteriorCrossDegrees.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.TripleCross.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem relativeExteriorCup_associative (X Y Z : TopCat) (A : Set X) (B : Set Y) (C : Set Z)
    (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) (p q r : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y B q)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Z C r) :
    ExteriorDegreeEvaluation.Constructions.exteriorAt (TopCat.of (X × Y)) Z (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) C
      ((hA.preimage continuous_fst).union (hB.preimage continuous_snd)) hC
      (p + q) r (p + (q + r)) (Nat.add_assoc p q r)
      (HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X Y A B hA hB p q a b) c =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (TripleCross.Constructions.spaceAssociate ((X, Y), Z)).hom
      (CrossAssociateForward.Constructions.leftSupportMapsTo ((X, Y), Z) A B C) (p + (q + r))
      (HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X (TopCat.of (Y × Z)) A (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement Y Z B C) hA
        ((hB.preimage continuous_fst).union (hC.preimage continuous_snd)) p (q + r) a
        (HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup Y Z B C hB hC q r b c)) := by
  let AB := HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B
  let BC := HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement Y Z B C
  let hAB := (hA.preimage continuous_fst).union (hB.preimage continuous_snd)
  let hBC := (hB.preimage continuous_fst).union (hC.preimage continuous_snd)
  let ab := HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X Y A B hA hB p q a b
  let bc := HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup Y Z B C hB hC q r b c
  let right := HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X (TopCat.of (Y × Z)) A BC hA hBC p (q + r) a bc
  apply (Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of ((X × Y) × Z))
    (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement (TopCat.of (X × Y)) Z AB C) (p + (q + r))).injective
  apply TripleCrossSpanning.Constructions.linearMap_ext X Y Z A B C hA hB hC (p + (q + r))
  intro i j k m hij hmk u v w
  rw [Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv_apply, Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv_apply]
  have hn := Geometric.RelativeUniversalCoefficientNaturality.Cycles.relativeHomologyEvaluation_naturality (ModuleCat.of ℚ ℚ)
    (X := TopCat.of ((X × Y) × Z)) (Y := TopCat.of (X × (Y × Z)))
    (TripleCross.Constructions.spaceAssociate ((X, Y), Z)).hom (CrossAssociateForward.Constructions.leftSupportMapsTo ((X, Y), Z) A B C) (p + (q + r)) right
    (CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ (TopCat.of (X × Y)) Z AB C m k (p + (q + r)) hmk
      (CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ X Y A B i j m hij u v) w)
  refine Eq.trans ?_ hn.symm
  by_cases hi : i = p
  · subst i
    have hjk : j + k = q + r := by omega
    have hc := ExteriorDegreeEvaluation.Constructions.cross_associate_at_targets X Y Z A B C p j k m (q + r) (p + (q + r)) hij hjk hmk u v w
    have hr := (congrArg (Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) (TopCat.of (X × (Y × Z)))
      (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X (TopCat.of (Y × Z)) A BC) (p + (q + r)) right) hc).trans
      (ExteriorDegreeEvaluation.Constructions.exteriorAt_cross_same X (TopCat.of (Y × Z)) A BC hA hBC p (q + r) (p + (q + r)) rfl a bc u
        (CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ Y Z B C j k (q + r) hjk v w))
    refine Eq.trans ?_ hr.symm
    by_cases hj : j = q
    · subst j
      have hk : k = r := by omega
      subst k
      subst m
      have hl := ExteriorDegreeEvaluation.Constructions.exteriorAt_cross_same (TopCat.of (X × Y)) Z AB C hAB hC
        (p + q) r (p + (q + r)) (Nat.add_assoc p q r) ab c
        (CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ X Y A B p q (p + q) rfl u v) w
      have h₁ := HodgeConjecture.DegreeTwo.ExteriorCupCrossEvaluation.Constructions.relativeExteriorCup_cross_evaluation X Y A B hA hB p q a b u v
      have h₂ := HodgeConjecture.DegreeTwo.ExteriorCupCrossEvaluation.Constructions.relativeExteriorCup_cross_evaluation Y Z B C hB hC q r b c v w
      exact hl.trans ((congrArg (fun z => z * Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) Z C r c w) h₁).trans
        ((mul_assoc _ _ _).trans (congrArg (fun z => Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) X A p a u * z) h₂.symm)))
    · have hm : m ≠ p + q := by omega
      have hl := ExteriorDegreeEvaluation.Constructions.exteriorAt_cross_other (TopCat.of (X × Y)) Z AB C hAB hC
        (p + q) r (p + (q + r)) (Nat.add_assoc p q r) m k hmk hm ab c
        (CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ X Y A B p j m hij u v) w
      have hz := ExteriorCrossDegrees.Constructions.exterior_cross_other Y Z B C hB hC q r j k hjk hj b c v w
      exact hl.trans ((congrArg (fun z => Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) X A p a u * z) hz).trans
        (mul_zero _)).symm
  · have hc := CrossAssociateForward.Constructions.cross_associate_at ℚ ((X, Y), Z) A B C i j k m (p + (q + r)) hij hmk u v w
    have hr := (congrArg (Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) (TopCat.of (X × (Y × Z)))
      (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X (TopCat.of (Y × Z)) A BC) (p + (q + r)) right) hc).trans
      (ExteriorCrossDegrees.Constructions.exterior_cross_other X (TopCat.of (Y × Z)) A BC hA hBC p (q + r) i (j + k) (by omega) hi a bc u
        (CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ Y Z B C j k (j + k) rfl v w))
    refine Eq.trans ?_ hr.symm
    by_cases hm : m = p + q
    · cases hm
      have hk : k = r := by omega
      subst k
      have hl := ExteriorDegreeEvaluation.Constructions.exteriorAt_cross_same (TopCat.of (X × Y)) Z AB C hAB hC
        (p + q) r (p + (q + r)) (Nat.add_assoc p q r) ab c
        (CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ X Y A B i j (p + q) hij u v) w
      have hz := ExteriorCrossDegrees.Constructions.exterior_cross_other X Y A B hA hB p q i j hij hi a b u v
      exact hl.trans ((congrArg (fun z => z * Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) Z C r c w) hz).trans
        (zero_mul _))
    · exact ExteriorDegreeEvaluation.Constructions.exteriorAt_cross_other (TopCat.of (X × Y)) Z AB C hAB hC
        (p + q) r (p + (q + r)) (Nat.add_assoc p q r) m k hmk hm ab c
        (CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ X Y A B i j m hij u v) w

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Relative.ExteriorAssociativity.Constructions
