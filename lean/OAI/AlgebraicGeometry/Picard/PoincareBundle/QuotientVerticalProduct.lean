import OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ProductTranslations
import OAI.AlgebraicGeometry.Picard.PoincareBundle.QuotientTransverseProduct

/-! # Quotient Vertical Product -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.QuotientVerticalProduct

noncomputable section

/-!
# The actual vertical quotient transports preserve the genuine vertical product
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Pair OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.AxisData
open OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateTransverseTranslations OAI.AlgebraicGeometry.Picard.PoincareBundle.QuotientTransverseProduct

variable {S : Scheme.{u}} {A X Y : Over S} [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (g : X ⟶ Y) [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left) (D : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (F : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g D) (hc : KernelFrame.Centrality.Central g F)

attribute [local instance] Kernel.Scheme.kernelGroup

include hc in
/-- The constructed vertical quotient transports satisfy the true vertical product equivariance equation. -/
theorem vertical_product {T : Over S} (z w u v : T ⟶ X) (a : T ⟶ A)
    (hz : z ≫ g = u ≫ g) (hw : w ≫ g = v ≫ g)
    (U : T.left.Opens) (m : Γ(Line.Fibers.fiber L (lift a z), U)) (n : Γ(Line.Fibers.fiber L (lift a w), U)) :
    (CoordinateTransverseTranslations.verticalProductTo L D u v (u * v) a rfl).app U
      ((Biextension.AxisData.vertical g L D F (lift a z) (lift a u) (QuotientTransverseProduct.liftedVertical g a z u hz)).app U m)
      ((Biextension.AxisData.vertical g L D F (lift a w) (lift a v) (QuotientTransverseProduct.liftedVertical g a w v hw)).app U n) =
    (Biextension.AxisData.vertical g L D F (lift a (z * w)) (lift a (u * v))
      (QuotientTransverseProduct.liftedVertical g a (z * w) (u * v) (Kernel.DifferenceProduct.product_images g z u w v hz hw))).app U
      ((CoordinateTransverseTranslations.verticalProductTo L D z w (z * w) a rfl).app U m n) := by
  let k := Kernel.Pair.pointDifference g z u hz
  let l := Kernel.Pair.pointDifference g w v hw
  have hk : (k ≫ Kernel.Scheme.kernelInclusion g) * z = u := QuotientHorizontalProduct.difference_left_translation g z u hz
  have hl : (l ≫ Kernel.Scheme.kernelInclusion g) * w = v := QuotientHorizontalProduct.difference_left_translation g w v hw
  have hkl := Product.TargetTranslations.combined_translation g k l z w u v (u * v) hk hl rfl
  rw [CoordinateQuotientTransport.vertical_eq g L D F k z u a _ hk,
    CoordinateQuotientTransport.vertical_eq g L D F l w v a _ hl,
    CoordinateQuotientTransport.vertical_eq g L D F (k * l) (z * w) (u * v) a _ hkl]
  exact Vertical.ProductTranslations.product_translations g L D F hc k l z w u v (u * v) a hk hl rfl U m n

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.QuotientVerticalProduct
