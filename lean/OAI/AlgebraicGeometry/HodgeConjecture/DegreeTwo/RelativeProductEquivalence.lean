import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCrossNonvanishing
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.WhitneyCrossHomotopySupport
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RationalSmallDescent

/-! # Relative Product Equivalence -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeProductEquivalence.Constructions

noncomputable section

/-!
# DegreeTwo: the actual relative product comparison is an equivalence

The reverse canonical homotopy descends through the genuine binary-small
quotient in every degree. Together with the already descended tensor-side
homotopy, this gives both inverse identities, not just nonvanishing.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open OAI.AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.ProductAlexanderWhitney

set_option backward.isDefEq.respectTransparency false

variable (X Y : TopCat.{0}) (A : Set X) (B : Set Y)

theorem smallWhitneyCross_projection :
    SmallProductComparison.Constructions.productSmallComplementProjection X Y A B ≫
      (SmallProductComparison.Constructions.smallRelativeAlexanderWhitney X Y A B ≫ SmallProductComparison.Constructions.smallRelativeChainCross X Y A B) =
    (AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.ProductAlexanderWhitney.productAw ℚ (X,Y) ≫ RelativeCrossSupport.Constructions.singularChainCross ℚ X Y) ≫
      SmallProductComparison.Constructions.productSmallComplementProjection X Y A B := by
  rw [← Category.assoc, SmallProductComparison.Constructions.smallRelativeAlexanderWhitney_projection,
    RelativeAlexanderWhitney.Constructions.relativeAlexanderWhitneyPre, Category.assoc, SmallProductComparison.Constructions.smallRelativeChainCross_projection,
    ← Category.assoc]

def smallWhitneyCrossHomotopy :
    Homotopy (SmallProductComparison.Constructions.smallRelativeAlexanderWhitney X Y A B ≫ SmallProductComparison.Constructions.smallRelativeChainCross X Y A B)
      (𝟙 (SmallProductComparison.Constructions.productSmallComplementChains X Y A B)) := by
  let π := SmallProductComparison.Constructions.productSmallComplementProjection X Y A B
  let H := WhitneyCrossHomotopySupport.Constructions.alexanderWhitneyCrossHomotopy ℚ X Y
  have : ∀ n, Epi (π.f n) := fun n => inferInstance
  have hA := RationalSmallDescent.Constructions.binaryRationalComplementProjection_left (TopCat.of (X×Y)) (Prod.fst ⁻¹' A) (Prod.snd ⁻¹' B)
  have hB := RationalSmallDescent.Constructions.binaryRationalComplementProjection_right (TopCat.of (X×Y)) (Prod.fst ⁻¹' A) (Prod.snd ⁻¹' B)
  have hl (a b : ℕ) :
      (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ (TopCat.of (X×Y)) (Prod.fst ⁻¹' A)).f a ≫
        H.hom a b ≫ π.f b = 0 :=
    WhitneyCrossHomotopySupport.Constructions.alexanderWhitneyCrossHomotopy_left_zero ℚ X Y A π hA a b
  have hr (a b : ℕ) :
      (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ (TopCat.of (X×Y)) (Prod.snd ⁻¹' B)).f a ≫
        H.hom a b ≫ π.f b = 0 :=
    WhitneyCrossHomotopySupport.Constructions.alexanderWhitneyCrossHomotopy_right_zero ℚ X Y B π hB a b
  refine QuotientHomotopy.Constructions.quotientHomotopyOfComponents π π (smallWhitneyCross_projection X Y A B)
    (by simp) H
    (fun a b => RationalSmallDescent.Constructions.binaryRationalComplementDegreeDesc (TopCat.of (X×Y))
      (Prod.fst ⁻¹' A) (Prod.snd ⁻¹' B) a (H.hom a b ≫ π.f b) (hl a b) (hr a b)) ?_
  intro a b
  exact RationalSmallDescent.Constructions.binaryRationalComplementDegreeDesc_projection (TopCat.of (X×Y))
    (Prod.fst ⁻¹' A) (Prod.snd ⁻¹' B) a (H.hom a b ≫ π.f b) (hl a b) (hr a b)

def relativeSmallProductHomotopyEquiv :
    HomotopyEquiv (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A ⊗ CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ Y B)
      (SmallProductComparison.Constructions.productSmallComplementChains X Y A B) where
  hom := SmallProductComparison.Constructions.smallRelativeChainCross X Y A B
  inv := SmallProductComparison.Constructions.smallRelativeAlexanderWhitney X Y A B
  homotopyHomInvId := RelativeCrossNonvanishing.Constructions.smallCrossWhitneyHomotopy X Y A B
  homotopyInvHomId := smallWhitneyCrossHomotopy X Y A B

theorem smallWhitneyCross_homology (n : ℕ) :
    HomologicalComplex.homologyMap (SmallProductComparison.Constructions.smallRelativeAlexanderWhitney X Y A B) n ≫
      HomologicalComplex.homologyMap (SmallProductComparison.Constructions.smallRelativeChainCross X Y A B) n = 𝟙 _ := by
  rw [← HomologicalComplex.homologyMap_comp,
    (smallWhitneyCrossHomotopy X Y A B).homologyMap_eq n,
    HomologicalComplex.homologyMap_id]

theorem relativeWhitneyCross_homology (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    SmallProductComparison.Constructions.relativeAlexanderWhitneyHomology X Y A B hA hB n ≫
      RelativeCrossProduct.Constructions.relativeSingularCrossHomology ℚ X Y A B n = 𝟙 _ := by
  let e := RationalSmallDescent.Constructions.binaryRationalComplementHomologyIso (TopCat.of (X×Y))
    (Prod.fst ⁻¹' A) (Prod.snd ⁻¹' B) (hA.preimage continuous_fst) (hB.preimage continuous_snd) n
  have hc : HomologicalComplex.homologyMap (SmallProductComparison.Constructions.smallRelativeChainCross X Y A B) n ≫ e.hom =
      RelativeCrossProduct.Constructions.relativeSingularCrossHomology ℚ X Y A B n := by
    change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n = _
    rw [← HomologicalComplex.homologyMap_comp, SmallProductComparison.Constructions.smallRelativeChainCross_to_relative]
    rfl
  change (e.inv ≫ HomologicalComplex.homologyMap (SmallProductComparison.Constructions.smallRelativeAlexanderWhitney X Y A B) n) ≫
    RelativeCrossProduct.Constructions.relativeSingularCrossHomology ℚ X Y A B n = _
  rw [← hc, Category.assoc, ← Category.assoc
    (HomologicalComplex.homologyMap (SmallProductComparison.Constructions.smallRelativeAlexanderWhitney X Y A B) n),
    smallWhitneyCross_homology, Category.id_comp, Iso.inv_hom_id]
  rfl

def relativeCrossHomologyIso (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A ⊗ CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ Y B).homology n ≅
      CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of (X×Y)) (RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) n where
  hom := RelativeCrossProduct.Constructions.relativeSingularCrossHomology ℚ X Y A B n
  inv := SmallProductComparison.Constructions.relativeAlexanderWhitneyHomology X Y A B hA hB n
  hom_inv_id := RelativeCrossNonvanishing.Constructions.relativeCrossWhitney_homology X Y A B hA hB n
  inv_hom_id := relativeWhitneyCross_homology X Y A B hA hB n

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeProductEquivalence.Constructions
