import OAI.AlgebraicGeometry.CycleClass.Thom.Relative.ExteriorCrossDegrees
import OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossAssociateForward

/-! # Exterior Degree Evaluation -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Relative.ExteriorDegreeEvaluation.Constructions

noncomputable section

/-! Explicit-degree evaluation of exterior classes and reassociation
of cross classes with an independently specified tail degree. -/

open _root_.CategoryTheory _root_.HomologicalComplex

open OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossAssociateForward.Constructions.HomologyAssociativity OAI.AlgebraicGeometry.CycleClass.Thom.Relative.ExteriorCrossDegrees.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossAssociateForward.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.TripleCross.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def exteriorAt (X Y : TopCat) (A : Set X) (B : Set Y) (hA : IsOpen A) (hB : IsOpen B)
    (p q n : ℕ) (h : p + q = n)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y B q) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X × Y)) (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) n :=
  eqToHom (congrArg (fun d => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of (X × Y)) (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) d) h) (HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X Y A B hA hB p q a b)

theorem exteriorAt_cross_same (X Y : TopCat) (A : Set X) (B : Set Y) (hA : IsOpen A) (hB : IsOpen B)
    (p q n : ℕ) (h : p + q = n)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y B q)
    (u : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ X A p) (v : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ Y B q) :
    Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) (TopCat.of (X × Y)) (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) n
      (exteriorAt X Y A B hA hB p q n h a b) (CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ X Y A B p q n h u v) =
    Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) X A p a u * Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) Y B q b v := by
  subst n
  exact HodgeConjecture.DegreeTwo.ExteriorCupCrossEvaluation.Constructions.relativeExteriorCup_cross_evaluation X Y A B hA hB p q a b u v

theorem exteriorAt_cross_other (X Y : TopCat) (A : Set X) (B : Set Y) (hA : IsOpen A) (hB : IsOpen B)
    (p q n : ℕ) (h : p + q = n) (i j : ℕ) (hij : i + j = n) (hi : i ≠ p)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y B q)
    (u : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ X A i) (v : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ Y B j) :
    Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) (TopCat.of (X × Y)) (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) n
      (exteriorAt X Y A B hA hB p q n h a b) (CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ X Y A B i j n hij u v) = 0 := by
  subst n
  exact ExteriorCrossDegrees.Constructions.exterior_cross_other X Y A B hA hB p q i j hij hi a b u v

theorem cross_associate_at_targets (X Y Z : TopCat) (A : Set X) (B : Set Y) (C : Set Z)
    (i j k m l n : ℕ) (hij : i + j = m) (hjk : j + k = l) (hmk : m + k = n)
    (a : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ X A i) (b : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ Y B j)
    (c : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ Z C k) :
    homologyMap (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (TripleCross.Constructions.spaceAssociate ((X, Y), Z)).hom (CrossAssociateForward.Constructions.leftSupportMapsTo ((X, Y), Z) A B C)) n
      (CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ (TopCat.of (X × Y)) Z (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) C m k n hmk
        (CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ X Y A B i j m hij a b) c) =
    CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ X (TopCat.of (Y × Z)) A (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement Y Z B C) i l n (by omega) a
      (CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ Y Z B C j k l hjk b c) := by
  subst m
  subst l
  exact CrossAssociateForward.Constructions.cross_associate ℚ ((X, Y), Z) A B C i j k n hmk a b c

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Relative.ExteriorDegreeEvaluation.Constructions
