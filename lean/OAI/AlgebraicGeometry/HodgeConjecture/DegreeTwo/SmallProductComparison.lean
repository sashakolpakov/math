import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCrossProduct
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CrossQuotientSupport
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RationalSmallDescent
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeAlexanderWhitney

/-! # Small Product Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmallProductComparison.Constructions

noncomputable section

/-!
# DegreeTwo: actual product comparison on the binary-small quotient

The cross product and canonical Alexander–Whitney map descend in opposite
directions. Both retain their actual formulas on quotient representatives.
The cross product agrees with the standard relative cross product through
the proved subdivision comparison.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory

set_option backward.isDefEq.respectTransparency false

variable (X Y : TopCat.{0}) (A : Set X) (B : Set Y)

abbrev productSmallComplementChains :=
  RationalSmallDescent.Constructions.binaryRationalComplementChains (TopCat.of (X × Y)) (Prod.fst ⁻¹' A) (Prod.snd ⁻¹' B)

abbrev productSmallComplementProjection :=
  RationalSmallDescent.Constructions.binaryRationalComplementProjection (TopCat.of (X × Y)) (Prod.fst ⁻¹' A) (Prod.snd ⁻¹' B)

def smallRelativeChainCross :
    CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A ⊗ CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ Y B ⟶
      productSmallComplementChains X Y A B :=
  TensorChainQuotient.Constructions.tensorChainQuotientDesc (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence ℚ X A) (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence ℚ Y B)
    (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence_shortExact ℚ X A) (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence_shortExact ℚ Y B)
    (RelativeCrossSupport.Constructions.singularChainCross ℚ X Y ≫ productSmallComplementProjection X Y A B)
    (CrossQuotientSupport.Constructions.singularChainCross_left_quotient_zero ℚ X Y A _
      (RationalSmallDescent.Constructions.binaryRationalComplementProjection_left _ _ _))
    (CrossQuotientSupport.Constructions.singularChainCross_right_quotient_zero ℚ X Y B _
      (RationalSmallDescent.Constructions.binaryRationalComplementProjection_right _ _ _))

theorem smallRelativeChainCross_projection :
    (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X A ⊗ₘ CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ Y B) ≫
      smallRelativeChainCross X Y A B =
    RelativeCrossSupport.Constructions.singularChainCross ℚ X Y ≫ productSmallComplementProjection X Y A B :=
  TensorChainQuotient.Constructions.tensorChainQuotientDesc_fac (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence ℚ X A) (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence ℚ Y B)
    (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence_shortExact ℚ X A) (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence_shortExact ℚ Y B)
    (RelativeCrossSupport.Constructions.singularChainCross ℚ X Y ≫ productSmallComplementProjection X Y A B)
    (CrossQuotientSupport.Constructions.singularChainCross_left_quotient_zero ℚ X Y A _
      (RationalSmallDescent.Constructions.binaryRationalComplementProjection_left _ _ _))
    (CrossQuotientSupport.Constructions.singularChainCross_right_quotient_zero ℚ X Y B _
      (RationalSmallDescent.Constructions.binaryRationalComplementProjection_right _ _ _))

def smallRelativeAlexanderWhitney : productSmallComplementChains X Y A B ⟶
    CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A ⊗ CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ Y B :=
  RationalSmallDescent.Constructions.binaryRationalComplementDesc _ _ _ (RelativeAlexanderWhitney.Constructions.relativeAlexanderWhitneyPre ℚ X Y A B)
    (RelativeAlexanderWhitney.Constructions.relativeAlexanderWhitneyPre_left ℚ X Y A B) (RelativeAlexanderWhitney.Constructions.relativeAlexanderWhitneyPre_right ℚ X Y A B)

theorem smallRelativeAlexanderWhitney_projection :
    productSmallComplementProjection X Y A B ≫ smallRelativeAlexanderWhitney X Y A B =
      RelativeAlexanderWhitney.Constructions.relativeAlexanderWhitneyPre ℚ X Y A B :=
  RationalSmallDescent.Constructions.binaryRationalComplementDesc_projection _ _ _ (RelativeAlexanderWhitney.Constructions.relativeAlexanderWhitneyPre ℚ X Y A B)
    (RelativeAlexanderWhitney.Constructions.relativeAlexanderWhitneyPre_left ℚ X Y A B) (RelativeAlexanderWhitney.Constructions.relativeAlexanderWhitneyPre_right ℚ X Y A B)

theorem smallRelativeChainCross_to_relative :
    smallRelativeChainCross X Y A B ≫
      RationalSmallDescent.Constructions.binaryRationalComplementToRelative (TopCat.of (X × Y)) (Prod.fst ⁻¹' A) (Prod.snd ⁻¹' B) =
      RelativeCrossProduct.Constructions.relativeSingularChainCross ℚ X Y A B := by
  have : Epi (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X A ⊗ₘ CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ Y B) :=
    HomologicalComplex.epi_of_epi_f _ (fun n => TensorChainQuotient.Constructions.tensorChainHom_degree_epi _ _ n)
  apply (cancel_epi (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X A ⊗ₘ CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ Y B)).mp
  rw [← Category.assoc, smallRelativeChainCross_projection, Category.assoc,
    RationalSmallDescent.Constructions.binaryRationalComplementToRelative_projection, RelativeCrossProduct.Constructions.relativeSingularChainCross_projection]
  rfl

/-- Reverse comparison on standard relative homology, using the inverse
of the proved small-to-all subdivision map. -/
def relativeAlexanderWhitneyHomology (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of (X × Y)) (RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) n ⟶
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A ⊗ CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ Y B).homology n :=
  (RationalSmallDescent.Constructions.binaryRationalComplementHomologyIso (TopCat.of (X × Y))
    (Prod.fst ⁻¹' A) (Prod.snd ⁻¹' B) (hA.preimage continuous_fst) (hB.preimage continuous_snd) n).inv ≫
    HomologicalComplex.homologyMap (smallRelativeAlexanderWhitney X Y A B) n

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmallProductComparison.Constructions
