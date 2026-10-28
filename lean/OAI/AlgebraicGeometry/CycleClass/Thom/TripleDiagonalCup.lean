import OAI.AlgebraicGeometry.CycleClass.Thom.Relative.ExteriorPairPullback
import OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossAssociateForward

/-! # Triple Diagonal Cup -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TripleDiagonalCup.Constructions

noncomputable section

/-! The two actual nested supported cups are the pullbacks of their
exterior counterparts under the two parenthesized triple diagonals. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.CycleClass.Thom.Relative.ExteriorPairPullback.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.TwoSupportCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normal.IntersectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.TripleCross.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : TopCat)

def leftTripleMap : X ⟶ TopCat.of ((X × X) × X) := Relative.ExteriorPairPullback.Constructions.pairMap (ImageIntersectionCup.Constructions.diagonalMap X) (𝟙 X)
def rightTripleMap : X ⟶ TopCat.of (X × (X × X)) := Relative.ExteriorPairPullback.Constructions.pairMap (𝟙 X) (ImageIntersectionCup.Constructions.diagonalMap X)

theorem tripleMap_associate : leftTripleMap X ≫ (TripleCross.Constructions.spaceAssociate ((X, X), X)).hom = rightTripleMap X := by
  ext x : 1
  rfl

variable (A B C : Set X)

theorem leftTriple_mapsTo : Set.MapsTo (leftTripleMap X) ((A ∪ B) ∪ C)
    (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement (TopCat.of (X × X)) X (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X X A B) C) :=
  Relative.ExteriorPairPullback.Constructions.pairMapsTo (ImageIntersectionCup.Constructions.diagonalMap X) (𝟙 X) (Normal.IntersectionCup.Constructions.diagonalComplementMapsTo X A B) (fun _ hx => hx)

theorem rightTriple_mapsTo : Set.MapsTo (rightTripleMap X) (A ∪ (B ∪ C))
    (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X (TopCat.of (X × X)) A (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X X B C)) :=
  Relative.ExteriorPairPullback.Constructions.pairMapsTo (𝟙 X) (ImageIntersectionCup.Constructions.diagonalMap X) (fun _ hx => hx) (Normal.IntersectionCup.Constructions.diagonalComplementMapsTo X B C)

theorem unionAssociate_mapsTo : Set.MapsTo (𝟙 X) ((A ∪ B) ∪ C) (A ∪ (B ∪ C)) := by
  intro x hx
  exact hx.elim (fun hab => hab.elim Or.inl (fun hb => Or.inr (Or.inl hb))) (fun hc => Or.inr (Or.inr hc))

variable (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) (p q r : ℕ)
  (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
  (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B q)
  (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X C r)

theorem leftTriple_pullback :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (leftTripleMap X) (leftTriple_mapsTo X A B C) ((p + q) + r)
      (HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup (TopCat.of (X × X)) X (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X X A B) C
        ((hA.preimage continuous_fst).union (hB.preimage continuous_snd)) hC (p + q) r
        (HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X X A B hA hB p q a b) c) =
    HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup X (A ∪ B) C (hA.union hB) hC (p + q) r
      (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup X A B hA hB p q a b) c := by
  have h := Relative.ExteriorPairPullback.Constructions.exterior_pullback_pairMap (ImageIntersectionCup.Constructions.diagonalMap X) (𝟙 X) (A ∪ B) C
    (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X X A B) C (hA.union hB) hC
    ((hA.preimage continuous_fst).union (hB.preimage continuous_snd)) hC
    (Normal.IntersectionCup.Constructions.diagonalComplementMapsTo X A B) (fun _ hx => hx) (p + q) r
    (HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X X A B hA hB p q a b) c
  exact h.trans (congrArg₂ (fun s t => HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup X (A ∪ B) C (hA.union hB) hC (p + q) r s t)
    (Intersection.TwoSupportCup.Constructions.diagonal_relativeExteriorCup X A B hA hB p q a b)
    (ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id (ModuleCat.of ℚ ℚ) X C r) c))

theorem rightTriple_pullback :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (rightTripleMap X) (rightTriple_mapsTo X A B C) (p + (q + r))
      (HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X (TopCat.of (X × X)) A (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X X B C) hA
        ((hB.preimage continuous_fst).union (hC.preimage continuous_snd)) p (q + r) a
        (HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X X B C hB hC q r b c)) =
    HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup X A (B ∪ C) hA (hB.union hC) p (q + r) a
      (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup X B C hB hC q r b c) := by
  have h := Relative.ExteriorPairPullback.Constructions.exterior_pullback_pairMap (𝟙 X) (ImageIntersectionCup.Constructions.diagonalMap X) A (B ∪ C)
    A (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X X B C) hA (hB.union hC) hA
    ((hB.preimage continuous_fst).union (hC.preimage continuous_snd))
    (fun _ hx => hx) (Normal.IntersectionCup.Constructions.diagonalComplementMapsTo X B C) p (q + r) a
    (HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X X B C hB hC q r b c)
  exact h.trans (congrArg₂ (fun s t => HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup X A (B ∪ C) hA (hB.union hC) p (q + r) s t)
    (ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id (ModuleCat.of ℚ ℚ) X A p) a)
    (Intersection.TwoSupportCup.Constructions.diagonal_relativeExteriorCup X B C hB hC q r b c))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TripleDiagonalCup.Constructions
