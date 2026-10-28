import OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossAssociateForward
import OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossSpanning
import OAI.AlgebraicGeometry.CycleClass.Thom.Relative.ExteriorCrossDegrees

/-! # Slant Exterior Associativity -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Relative.SlantExteriorAssociativity.Constructions

noncomputable section

/-! Slant along the last factor commutes with an exterior cup on the first factor. -/

open _root_.CategoryTheory _root_.HomologicalComplex

open OAI.AlgebraicGeometry.CycleClass.Thom.Relative.Slant.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossAssociateForward.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Relative.ExteriorCrossDegrees.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossAssociateForward.Constructions.HomologyAssociativity OAI.AlgebraicGeometry.CycleClass.Thom.TripleCross.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem slant_exterior_associate (X Y Z : TopCat.{0}) (A : Set X) (B : Set Y) (C : Set Z)
    (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) (p q r : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Y × Z))
      (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement Y Z B C) (q + r))
    (b : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ Z C r) :
    Slant.Constructions.slant ℚ (TopCat.of (X × Y)) Z (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) C
      (p + q) r (p + (q + r)) (Nat.add_assoc p q r) b
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (TripleCross.Constructions.spaceAssociate ((X, Y), Z)).hom (CrossAssociateForward.Constructions.leftSupportMapsTo ((X, Y), Z) A B C)
        (p + (q + r))
        (HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X (TopCat.of (Y × Z)) A (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement Y Z B C)
          hA ((hB.preimage continuous_fst).union (hC.preimage continuous_snd))
          p (q + r) a c)) =
      HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X Y A B hA hB p q a (Slant.Constructions.slant ℚ Y Z B C q r (q + r) rfl b c) := by
  apply (Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of (X × Y))
    (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) (p + q)).injective
  apply CrossSpanning.Constructions.linearMap_ext X Y A B hA hB (p + q)
  intro i j hij u v
  rw [Slant.Constructions.slant_evaluation, Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv_apply]
  have hn := Geometric.RelativeUniversalCoefficientNaturality.Cycles.relativeHomologyEvaluation_naturality (ModuleCat.of ℚ ℚ)
    (X := TopCat.of ((X × Y) × Z)) (Y := TopCat.of (X × (Y × Z)))
    (TripleCross.Constructions.spaceAssociate ((X, Y), Z)).hom (CrossAssociateForward.Constructions.leftSupportMapsTo ((X, Y), Z) A B C)
    (p + (q + r))
    (HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X (TopCat.of (Y × Z)) A (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement Y Z B C)
      hA ((hB.preimage continuous_fst).union (hC.preimage continuous_snd)) p (q + r) a c)
    (CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ (TopCat.of (X × Y)) Z (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) C
      (p + q) r (p + (q + r)) (Nat.add_assoc p q r)
      (CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ X Y A B i j (p + q) hij u v) b)
  refine hn.trans ?_
  rw [CrossAssociateForward.Constructions.cross_associate_at, Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv_apply]
  by_cases hi : i = p
  · subst i
    have hj : j = q := by omega
    subst j
    refine (HodgeConjecture.DegreeTwo.ExteriorCupCrossEvaluation.Constructions.relativeExteriorCup_cross_evaluation X (TopCat.of (Y × Z)) A
      (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement Y Z B C) hA
      ((hB.preimage continuous_fst).union (hC.preimage continuous_snd)) p (q + r) a c u
      (CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ Y Z B C q r (q + r) rfl v b)).trans ?_
    refine (congrArg (fun z => Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) X A p a u * z)
      (Slant.Constructions.slant_evaluation ℚ Y Z B C q r (q + r) rfl b c v).symm).trans ?_
    exact (HodgeConjecture.DegreeTwo.ExteriorCupCrossEvaluation.Constructions.relativeExteriorCup_cross_evaluation X Y A B hA hB p q a
      (Slant.Constructions.slant ℚ Y Z B C q r (q + r) rfl b c) u v).symm
  · exact (ExteriorCrossDegrees.Constructions.exterior_cross_other X (TopCat.of (Y × Z)) A (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement Y Z B C)
      hA ((hB.preimage continuous_fst).union (hC.preimage continuous_snd))
      p (q + r) i (j + r) (by omega) hi a c u
      (CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ Y Z B C j r (j + r) rfl v b)).trans
      (ExteriorCrossDegrees.Constructions.exterior_cross_other X Y A B hA hB p q i j hij hi a
        (Slant.Constructions.slant ℚ Y Z B C q r (q + r) rfl b c) u v).symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Relative.SlantExteriorAssociativity.Constructions
