import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

/-! # Relation Swap -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Product.RelationSwap.Construction

/-! Swapping the inputs of a product relation in a commutative group
preserves the actual product and its fixed coordinate. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

universe u

theorem productRel_swap {S : Scheme.{u}} {E A X T : Over S} [GrpObj A] [IsCommMonObj A]
    {p : E ⟶ A} {r : E ⟶ X} {a b c : T ⟶ E} (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel p r a b c) :
    Picard.PoincareBundle.FiberwiseMultiplication.ProductRel p r b a c :=
  ⟨(mul_comm _ _).trans h.1, h.2.1.symm, h.2.1.symm.trans h.2.2⟩

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Product.RelationSwap.Construction
