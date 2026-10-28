import OAI.AlgebraicGeometry.Picard.PoincareBundle.QuotientHorizontalProduct
import OAI.AlgebraicGeometry.Picard.PoincareBundle.TransverseTargetTranslations

/-! # Quotient Transverse Product -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.QuotientTransverseProduct

noncomputable section

/-!
# The constructed quotient transports respect multiplication in the transverse coordinate
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Pair OAI.AlgebraicGeometry.Picard.PoincareBundle.RectangularCoordinates
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.AxisData OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateProductTranslations OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateTransverseTranslations
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesTransverseTransport OAI.AlgebraicGeometry.Picard.PoincareBundle.QuotientHorizontalProduct

variable {S : Scheme.{u}} {A B X Y : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj X] [IsCommMonObj X]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (hi : Biextension.Compatibility.Interchange L Dh Dv)

section VerticalTranslations

variable [GrpObj Y] (g : X ⟶ Y) [IsMonHom g] (Fv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)
  (ht : Kernel.FramesTransverseTransport.Transverse g Fv Dh)

omit [GrpObj A] [IsCommMonObj A] [GrpObj X] [IsCommMonObj X] [GrpObj Y] [IsMonHom g] in
/-- Equal second-coordinate quotient images give the vertical relation of the actual lifted points. -/
theorem liftedVertical {T : Over S} (x : T ⟶ A) (z w : T ⟶ X) (h : z ≫ g = w ≫ g) :
    RectangularCoordinates.Vertical g (lift x z) (lift x w) := by
  constructor
  · simp only [lift_fst]
  · simpa only [← Category.assoc, lift_snd] using h

include hi ht in
omit [IsCommMonObj A] in
/-- The horizontal product is equivariant for the actual vertical quotient transport. -/
theorem horizontal_product {T : Over S} (x y : T ⟶ A) (z w : T ⟶ X) (h : z ≫ g = w ≫ g)
    (U : T.left.Opens) (m : Γ(Line.Fibers.fiber L (lift x z), U)) (n : Γ(Line.Fibers.fiber L (lift y z), U)) :
    (CoordinateProductTranslations.productTo L Dh x y (x * y) w rfl).app U
      ((Biextension.AxisData.vertical g L Dv Fv (lift x z) (lift x w) (liftedVertical g x z w h)).app U m)
      ((Biextension.AxisData.vertical g L Dv Fv (lift y z) (lift y w) (liftedVertical g y z w h)).app U n) =
    (Biextension.AxisData.vertical g L Dv Fv (lift (x * y) z) (lift (x * y) w) (liftedVertical g (x * y) z w h)).app U
      ((CoordinateProductTranslations.productTo L Dh x y (x * y) z rfl).app U m n) := by
  let l := Kernel.Pair.pointDifference g z w h
  have hl : (l ≫ Kernel.Scheme.kernelInclusion g) * z = w := QuotientHorizontalProduct.difference_left_translation g z w h
  rw [CoordinateQuotientTransport.vertical_eq g L Dv Fv l z w x _ hl,
    CoordinateQuotientTransport.vertical_eq g L Dv Fv l z w y _ hl,
    CoordinateQuotientTransport.vertical_eq g L Dv Fv l z w (x * y) _ hl]
  exact TransverseTargetTranslations.horizontal_product_to L Dh Dv hi g Fv ht l x y z w hl U m n

end VerticalTranslations

variable [GrpObj B] (f : A ⟶ B) [IsMonHom f] (Fh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh)
  (ht : Kernel.FramesTransverseTransport.Transverse f Fh Dv)

include hi ht in
omit [IsCommMonObj X] in
/-- The vertical product is equivariant for the actual horizontal quotient transport. -/
theorem vertical_product {T : Over S} (x u : T ⟶ A) (z w : T ⟶ X) (h : x ≫ f = u ≫ f)
    (U : T.left.Opens) (m : Γ(Line.Fibers.fiber L (lift x z), U)) (n : Γ(Line.Fibers.fiber L (lift x w), U)) :
    (CoordinateTransverseTranslations.verticalProductTo L Dv z w (z * w) u rfl).app U
      ((Biextension.AxisData.horizontal f L Dh Fh (lift x z) (lift u z) (QuotientHorizontalProduct.liftedHorizontal f x u z h)).app U m)
      ((Biextension.AxisData.horizontal f L Dh Fh (lift x w) (lift u w) (QuotientHorizontalProduct.liftedHorizontal f x u w h)).app U n) =
    (Biextension.AxisData.horizontal f L Dh Fh (lift x (z * w)) (lift u (z * w)) (QuotientHorizontalProduct.liftedHorizontal f x u (z * w) h)).app U
      ((CoordinateTransverseTranslations.verticalProductTo L Dv z w (z * w) x rfl).app U m n) := by
  let k := Kernel.Pair.pointDifference f x u h
  have hk : (k ≫ Kernel.Scheme.kernelInclusion f) * x = u := QuotientHorizontalProduct.difference_left_translation f x u h
  rw [CoordinateQuotientTransport.horizontal_eq f L Dh Fh k x u z _ hk,
    CoordinateQuotientTransport.horizontal_eq f L Dh Fh k x u w _ hk,
    CoordinateQuotientTransport.horizontal_eq f L Dh Fh k x u (z * w) _ hk]
  exact TransverseTargetTranslations.vertical_product_to L Dh Dv hi f Fh ht k x u z w hk U m n

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.QuotientTransverseProduct
