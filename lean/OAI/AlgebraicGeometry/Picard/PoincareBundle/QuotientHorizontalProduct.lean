import OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateQuotientTransport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.TargetTranslations

/-! # Quotient Horizontal Product -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.QuotientHorizontalProduct

noncomputable section

/-!
# The actual horizontal quotient transports preserve the actual horizontal line product
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Pair OAI.AlgebraicGeometry.Picard.PoincareBundle.RectangularCoordinates
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.AxisData OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateProductTranslations

variable {S : Scheme.{u}} {A B X : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f]

omit [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsMonHom f] in
/-- Equal first-coordinate quotient images give the actual horizontal relation between the lifted points. -/
theorem liftedHorizontal {T : Over S} (x u : T ⟶ A) (z : T ⟶ X) (h : x ≫ f = u ≫ f) :
    RectangularCoordinates.Horizontal f (lift x z) (lift u z) := by
  constructor
  · simpa only [← Category.assoc, lift_fst] using h
  · simp only [lift_snd]

/-- The included represented difference is the actual left translation between equal-image points. -/
theorem difference_left_translation {T : Over S} (x u : T ⟶ A) (h : x ≫ f = u ≫ f) :
    (Kernel.Pair.pointDifference f x u h ≫ Kernel.Scheme.kernelInclusion f) * x = u :=
  (mul_comm _ _).trans (Kernel.Linearization.difference_translates f x u h)

variable (L : Line.Bundles.LineBundle (A ⊗ X).left) (D : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L)
  (F : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f D) (hc : KernelFrame.Centrality.Central f F)

attribute [local instance] Kernel.Scheme.kernelGroup

include hc in
/-- The constructed horizontal quotient transports satisfy the true product equivariance equation. -/
theorem horizontal_product {T : Over S} (x y u v : T ⟶ A) (z : T ⟶ X)
    (hx : x ≫ f = u ≫ f) (hy : y ≫ f = v ≫ f)
    (U : T.left.Opens) (m : Γ(Line.Fibers.fiber L (lift x z), U)) (n : Γ(Line.Fibers.fiber L (lift y z), U)) :
    (CoordinateProductTranslations.productTo L D u v (u * v) z rfl).app U
      ((Biextension.AxisData.horizontal f L D F (lift x z) (lift u z) (liftedHorizontal f x u z hx)).app U m)
      ((Biextension.AxisData.horizontal f L D F (lift y z) (lift v z) (liftedHorizontal f y v z hy)).app U n) =
    (Biextension.AxisData.horizontal f L D F (lift (x * y) z) (lift (u * v) z)
      (liftedHorizontal f (x * y) (u * v) z (Kernel.DifferenceProduct.product_images f x u y v hx hy))).app U
      ((CoordinateProductTranslations.productTo L D x y (x * y) z rfl).app U m n) := by
  let k := Kernel.Pair.pointDifference f x u hx
  let l := Kernel.Pair.pointDifference f y v hy
  have hk : (k ≫ Kernel.Scheme.kernelInclusion f) * x = u := difference_left_translation f x u hx
  have hl : (l ≫ Kernel.Scheme.kernelInclusion f) * y = v := difference_left_translation f y v hy
  have hkl := Product.TargetTranslations.combined_translation f k l x y u v (u * v) hk hl rfl
  rw [CoordinateQuotientTransport.horizontal_eq f L D F k x u z _ hk,
    CoordinateQuotientTransport.horizontal_eq f L D F l y v z _ hl,
    CoordinateQuotientTransport.horizontal_eq f L D F (k * l) (x * y) (u * v) z _ hkl]
  exact Product.TargetTranslations.product_translations f L D F hc k l x y u v (u * v) z hk hl rfl U m n

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.QuotientHorizontalProduct
