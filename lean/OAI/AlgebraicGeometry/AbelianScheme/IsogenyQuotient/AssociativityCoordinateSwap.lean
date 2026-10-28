import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AssociativeParameterFactors

/-! # Associativity Coordinate Swap -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AssociativityCoordinateSwap.Construction

/-! Exchanging the two scheme coordinates carries actual product
relations and universal factor equations to the vertical direction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

universe u

variable {S : Scheme.{u}} {G X T : Over S} [GrpObj G]

theorem horizontalProductRel_coordinateSwap {a b c : T ⟶ G ⊗ X}
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst G X) (snd G X) a b c) :
    Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd X G) (fst X G) (a ≫ (β_ G X).hom) (b ≫ (β_ G X).hom) (c ≫ (β_ G X).hom) := by
  simpa only [Picard.PoincareBundle.FiberwiseMultiplication.ProductRel, Category.assoc, braiding_hom_fst, braiding_hom_snd] using h

theorem verticalProductRel_coordinateSwap {a b c : T ⟶ X ⊗ G}
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd X G) (fst X G) a b c) :
    Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst G X) (snd G X) (a ≫ (β_ X G).hom) (b ≫ (β_ X G).hom) (c ≫ (β_ X G).hom) := by
  simpa only [Picard.PoincareBundle.FiberwiseMultiplication.ProductRel, Category.assoc, braiding_hom_fst, braiding_hom_snd] using h

omit [GrpObj G] in
theorem associativeCoordinateSwap_factor {R : Over S} (r : T ⟶ R) (v : R ⟶ G ⊗ X) (d : T ⟶ X ⊗ G)
    (h : r ≫ v = d ≫ (β_ X G).hom) : r ≫ (v ≫ (β_ G X).hom) = d := by
  rw [← Category.assoc, h, Category.assoc]
  simp

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AssociativityCoordinateSwap.Construction
