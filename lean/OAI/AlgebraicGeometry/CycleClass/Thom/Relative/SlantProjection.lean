import OAI.AlgebraicGeometry.CycleClass.Thom.Relative.SlantExteriorAssociativity
import OAI.AlgebraicGeometry.CycleClass.Thom.Relative.SlantNaturality
import OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.TwoSupportCup

/-! # Slant Projection -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Relative.SlantProjection.Constructions

noncomputable section

/-! Supported projection formula, expressed through the actual graph and diagonal pullbacks. -/

open _root_.CategoryTheory _root_.HomologicalComplex
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels

open OAI.AlgebraicGeometry.CycleClass.Thom.Relative.Slant.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Relative.SlantNaturality.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Relative.SlantExteriorAssociativity.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossAssociateForward.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.TripleCross.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normal.Product.Constructions.Class
open OAI.AlgebraicGeometry.CycleClass.Thom.Normal.IntersectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.TwoSupportCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def projectionDoubleMap (X Z : TopCat.{0}) : TopCat.of (X × Z) ⟶ TopCat.of ((X × X) × Z) :=
  AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((ImageIntersectionCup.Constructions.diagonalMap X, 𝟙 Z) : (X, Z) ⟶ (TopCat.of (X × X), Z))

def projectionGraphMap (X Z : TopCat.{0}) : TopCat.of (X × Z) ⟶ TopCat.of (X × (X × Z)) :=
  projectionDoubleMap X Z ≫ (TripleCross.Constructions.spaceAssociate ((X, X), Z)).hom

theorem projectionDoubleMapsTo (X Z : TopCat.{0}) (A B : Set X) (C : Set Z) :
    Set.MapsTo (projectionDoubleMap X Z) (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Z (A ∪ B) C)
      (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement (TopCat.of (X × X)) Z (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X X A B) C) :=
  HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.crossSupportComplement_mapsTo (ImageIntersectionCup.Constructions.diagonalMap X) (𝟙 Z) (Normal.IntersectionCup.Constructions.diagonalComplementMapsTo X A B)
    (fun _ hx => hx)

theorem projectionGraphMapsTo (X Z : TopCat.{0}) (A B : Set X) (C : Set Z) :
    Set.MapsTo (projectionGraphMap X Z) (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Z (A ∪ B) C)
      (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X (TopCat.of (X × Z)) A (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Z B C)) :=
  (CrossAssociateForward.Constructions.leftSupportMapsTo ((X, X), Z) A B C).comp (projectionDoubleMapsTo X Z A B C)

theorem slant_graph (X Z : TopCat.{0}) (A B : Set X) (C : Set Z)
    (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) (p q r : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X × Z))
      (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Z B C) (q + r))
    (b : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ Z C r) :
    Slant.Constructions.slant ℚ X Z (A ∪ B) C (p + q) r (p + (q + r)) (Nat.add_assoc p q r) b
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (projectionGraphMap X Z)
        (projectionGraphMapsTo X Z A B C) (p + (q + r))
        (HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X (TopCat.of (X × Z)) A (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Z B C)
          hA ((hB.preimage continuous_fst).union (hC.preimage continuous_snd)) p (q + r) a c)) =
      HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup X A B hA hB p q a (Slant.Constructions.slant ℚ X Z B C q r (q + r) rfl b c) := by
  let e := HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X (TopCat.of (X × Z)) A (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Z B C)
    hA ((hB.preimage continuous_fst).union (hC.preimage continuous_snd)) p (q + r) a c
  have hc := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
      (projectionDoubleMap X Z) (TripleCross.Constructions.spaceAssociate ((X, X), Z)).hom
      (projectionDoubleMapsTo X Z A B C) (CrossAssociateForward.Constructions.leftSupportMapsTo ((X, X), Z) A B C)
      (p + (q + r))) e
  have hn := SlantNaturality.Constructions.slant_natural ℚ (ImageIntersectionCup.Constructions.diagonalMap X) (𝟙 Z)
    (Normal.IntersectionCup.Constructions.diagonalComplementMapsTo X A B) (A := A ∪ B) (B := C) (B' := C) (fun _ hx => hx)
    (p + q) r (p + (q + r)) (Nat.add_assoc p q r) b
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (TripleCross.Constructions.spaceAssociate ((X, X), Z)).hom
      (CrossAssociateForward.Constructions.leftSupportMapsTo ((X, X), Z) A B C) (p + (q + r)) e)
  simp only [Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap_id, homologyMap_id, CategoryTheory.id_apply] at hn
  have hs := SlantExteriorAssociativity.Constructions.slant_exterior_associate X X Z A B C hA hB hC p q r a c b
  refine (congrArg (Slant.Constructions.slant ℚ X Z (A ∪ B) C (p + q) r (p + (q + r))
    (Nat.add_assoc p q r) b) hc).symm.trans ?_
  refine hn.trans ?_
  exact (congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
    (ImageIntersectionCup.Constructions.diagonalMap X) (Normal.IntersectionCup.Constructions.diagonalComplementMapsTo X A B) (p + q)) hs).trans
    (Intersection.TwoSupportCup.Constructions.diagonal_relativeExteriorCup X A B hA hB p q a _)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Relative.SlantProjection.Constructions
