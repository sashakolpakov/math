import OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossSpanning

/-! # Triple Cross Spanning -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Relative.TripleCrossSpanning.Constructions

noncomputable section

/-! Iterated genuine relative cross classes span triple-product
homology, with all factor degrees retained. -/

open _root_.CategoryTheory _root_.HomologicalComplex
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossAssociateForward.Constructions.HomologyAssociativity OAI.AlgebraicGeometry.CycleClass.Thom.HomologyProductAssociativity.Constructions.Products

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def relativeCrossLeftLinear (X Y : TopCat) (A : Set X) (B : Set Y) (p q n : ℕ) (h : p + q = n)
    (b : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ Y B q) :
    Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ X A p →ₗ[ℚ]
      Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of (X × Y)) (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) n where
  toFun a := CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ X Y A B p q n h a b
  map_add' a a' := by
    simp only [CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt, HomologyProductAssociativity.Constructions.Products.homologyProduct, TensorProduct.add_tmul, map_add]
  map_smul' r a := by
    simp only [CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt, HomologyProductAssociativity.Constructions.Products.homologyProduct, ← TensorProduct.smul_tmul', map_smul]
    rfl

theorem linearMap_ext (X Y Z : TopCat) (A : Set X) (B : Set Y) (C : Set Z)
    (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) (n : ℕ)
    {M : Type} [AddCommGroup M] [Module ℚ M]
    (F G : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of ((X × Y) × Z))
      (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement (TopCat.of (X × Y)) Z (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) C) n →ₗ[ℚ] M)
    (h : ∀ (i j k m : ℕ) (hij : i + j = m) (hmk : m + k = n)
      (a : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ X A i) (b : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ Y B j)
      (c : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ Z C k),
      F (CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ (TopCat.of (X × Y)) Z (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) C m k n hmk
          (CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ X Y A B i j m hij a b) c) =
        G (CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ (TopCat.of (X × Y)) Z (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) C m k n hmk
          (CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ X Y A B i j m hij a b) c)) : F = G := by
  apply CrossSpanning.Constructions.linearMap_ext (TopCat.of (X × Y)) Z
    (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) C ((hA.preimage continuous_fst).union (hB.preimage continuous_snd)) hC n
  intro m k hmk v c
  let L := relativeCrossLeftLinear (TopCat.of (X × Y)) Z (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) C m k n hmk c
  have he : F.comp L = G.comp L := by
    apply CrossSpanning.Constructions.linearMap_ext X Y A B hA hB m
    intro i j hij a b
    exact h i j k m hij hmk a b c
  exact LinearMap.congr_fun he v

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Relative.TripleCrossSpanning.Constructions
