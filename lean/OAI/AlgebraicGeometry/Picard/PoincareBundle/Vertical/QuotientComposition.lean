import OAI.AlgebraicGeometry.Picard.PoincareBundle.QuotientVerticalProduct
import OAI.AlgebraicGeometry.Picard.PoincareBundle.QuotientProductComposition

/-! # Quotient Composition -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.QuotientComposition

noncomputable section

/-!
# The full actual quotient transport preserves the vertical biextension product
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.AxisData OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateTransverseTranslations
open OAI.AlgebraicGeometry.Picard.PoincareBundle.QuotientProductComposition OAI.AlgebraicGeometry.Picard.PoincareBundle.QuotientHorizontalProduct OAI.AlgebraicGeometry.Picard.PoincareBundle.QuotientTransverseProduct
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesTransverseTransport

variable {S : Scheme.{u}} {A B X Y : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (f : A ⟶ B) (g : X ⟶ Y) [IsMonHom f] [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh) (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)
  (hi : Biextension.Compatibility.Interchange L Dh Dv)
  (hc : KernelFrame.Centrality.Central g Kv) (ht : Kernel.FramesTransverseTransport.Transverse f Kh Dv)

include hi hc ht in
/-- The genuine vertical product is equivariant under the complete constructed quotient transport. -/
theorem vertical_product {T : Over S} (a b : T ⟶ A) (z w u v : T ⟶ X)
    (ha : a ≫ f = b ≫ f) (hz : z ≫ g = u ≫ g) (hw : w ≫ g = v ≫ g)
    (U : T.left.Opens) (m : Γ(Line.Fibers.fiber L (lift a z), U)) (n : Γ(Line.Fibers.fiber L (lift a w), U)) :
    (CoordinateTransverseTranslations.verticalProductTo L Dv u v (u * v) b rfl).app U
      ((QuotientProductComposition.coordinateTotal f g L Dh Dv Kh Kv a b z u ha hz).app U m)
      ((QuotientProductComposition.coordinateTotal f g L Dh Dv Kh Kv a b w v ha hw).app U n) =
    (QuotientProductComposition.coordinateTotal f g L Dh Dv Kh Kv a b (z * w) (u * v) ha
      (Kernel.DifferenceProduct.product_images g z u w v hz hw)).app U
      ((CoordinateTransverseTranslations.verticalProductTo L Dv z w (z * w) a rfl).app U m n) := by
  change (CoordinateTransverseTranslations.verticalProductTo L Dv u v (u * v) b rfl).app U
      ((Biextension.AxisData.vertical g L Dv Kv _ _ (QuotientTransverseProduct.liftedVertical g b z u hz)).app U
        ((Biextension.AxisData.horizontal f L Dh Kh _ _ (QuotientHorizontalProduct.liftedHorizontal f a b z ha)).app U m))
      ((Biextension.AxisData.vertical g L Dv Kv _ _ (QuotientTransverseProduct.liftedVertical g b w v hw)).app U
        ((Biextension.AxisData.horizontal f L Dh Kh _ _ (QuotientHorizontalProduct.liftedHorizontal f a b w ha)).app U n)) =
    (Biextension.AxisData.vertical g L Dv Kv _ _ (QuotientTransverseProduct.liftedVertical g b (z * w) (u * v)
      (Kernel.DifferenceProduct.product_images g z u w v hz hw))).app U
      ((Biextension.AxisData.horizontal f L Dh Kh _ _ (QuotientHorizontalProduct.liftedHorizontal f a b (z * w) ha)).app U
        ((CoordinateTransverseTranslations.verticalProductTo L Dv z w (z * w) a rfl).app U m n))
  rw [QuotientVerticalProduct.vertical_product g L Dv Kv hc z w u v b hz hw,
    QuotientTransverseProduct.vertical_product L Dh Dv hi f Kh ht a b z w ha]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.QuotientComposition
