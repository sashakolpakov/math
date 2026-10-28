import OAI.AlgebraicGeometry.CycleClass.Thom.Relative.Slant
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeProductEquivalence

/-! # Cross Spanning -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossSpanning.Constructions

noncomputable section

/-! Actual relative cross classes span product homology for open complements. -/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeProductEquivalence.Constructions
open scoped TensorProduct DirectSum

open OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossAssociateForward.Constructions.HomologyAssociativity OAI.AlgebraicGeometry.CycleClass.Thom.HomologyProductAssociativity.Constructions.Products

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem linearMap_ext (X Y : TopCat.{0}) (A : Set X) (B : Set Y)
    (hA : IsOpen A) (hB : IsOpen B) (n : ℕ)
    {V : Type} [AddCommGroup V] [Module ℚ V]
    (F G : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of (X × Y))
      (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) n →ₗ[ℚ] V)
    (h : ∀ (p q : ℕ) (hpq : p + q = n)
      (a : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ X A p) (b : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ Y B q),
      F (CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ X Y A B p q n hpq a b) =
        G (CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ X Y A B p q n hpq a b)) : F = G := by
  let e := (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.algebraicKunneth (Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A) (Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ Y B) n).trans
    (HodgeConjecture.DegreeTwo.RelativeProductEquivalence.Constructions.relativeCrossHomologyIso X Y A B hA hB n).toLinearEquiv
  apply (LinearMap.cancel_right e.surjective).mp
  apply DirectSum.linearMap_ext
  intro ij
  apply TensorProduct.ext'
  intro a b
  exact h ij.val.1 ij.val.2 ij.property a b

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossSpanning.Constructions
