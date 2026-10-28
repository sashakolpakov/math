import OAI.AlgebraicGeometry.Picard.PoincareBundle.QuotientTransverseProduct

/-! # Quotient Product Composition -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.QuotientProductComposition

noncomputable section

/-!
# The full actual quotient transport preserves the horizontal biextension product
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.RectangularCoordinates OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.AxisData
open OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateProductTranslations OAI.AlgebraicGeometry.Picard.PoincareBundle.QuotientHorizontalProduct OAI.AlgebraicGeometry.Picard.PoincareBundle.QuotientTransverseProduct
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesTransverseTransport

variable {S : Scheme.{u}} {A B X Y : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (f : A ⟶ B) (g : X ⟶ Y) [IsMonHom f] [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh) (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)

/-- The actual coordinate composite first uses horizontal quotient transport and then vertical quotient transport. -/
def coordinateTotal {T : Over S} (x u : T ⟶ A) (z w : T ⟶ X)
    (hx : x ≫ f = u ≫ f) (hz : z ≫ g = w ≫ g) : Line.Fibers.fiber L (lift x z) ⟶ Line.Fibers.fiber L (lift u w) :=
  Biextension.AxisData.horizontal f L Dh Kh (lift x z) (lift u z) (QuotientHorizontalProduct.liftedHorizontal f x u z hx) ≫
    Biextension.AxisData.vertical g L Dv Kv (lift u z) (lift u w) (QuotientTransverseProduct.liftedVertical g u z w hz)

omit [GrpObj A] [IsCommMonObj A] [GrpObj B] [GrpObj X] [IsCommMonObj X] [GrpObj Y] [IsMonHom f] [IsMonHom g] in
/-- Equal component quotient images give equal images under the actual product quotient map. -/
theorem product_images {T : Over S} (x u : T ⟶ A) (z w : T ⟶ X)
    (hx : x ≫ f = u ≫ f) (hz : z ≫ g = w ≫ g) : lift x z ≫ (f ⊗ₘ g) = lift u w ≫ (f ⊗ₘ g) := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [hx, hz]

/-- The full ordinary product transport is exactly the two actual coordinate maps on lifted points. -/
theorem native_total {T : Over S} (x u : T ⟶ A) (z w : T ⟶ X)
    (hx : x ≫ f = u ≫ f) (hz : z ≫ g = w ≫ g) :
    RectangularTransport.total f g (Geometric.KernelLinearization.overModulePullbacks S) L.sheaf (Biextension.AxisData.toAxisData f g L Dh Dv Kh Kv)
      (lift x z) (lift u w) (product_images f g x u z w hx hz) = coordinateTotal f g L Dh Dv Kh Kv x u z w hx hz := by
  have he (m : T ⟶ A ⊗ X) (hm : m = lift u z) (h₁ : RectangularCoordinates.Horizontal f (lift x z) m) (h₂ : RectangularCoordinates.Vertical g m (lift u w)) :
      Biextension.AxisData.horizontal f L Dh Kh (lift x z) m h₁ ≫ Biextension.AxisData.vertical g L Dv Kv m (lift u w) h₂ =
        coordinateTotal f g L Dh Dv Kh Kv x u z w hx hz := by
    subst m
    rfl
  exact he (RectangularCoordinates.middle (lift x z) (lift u w)) (by simp only [RectangularCoordinates.middle, lift_fst, lift_snd])
    (RectangularCoordinates.horizontal_middle f g _ _ (product_images f g x u z w hx hz))
    (RectangularCoordinates.vertical_middle f g _ _ (product_images f g x u z w hx hz))

variable (hi : Biextension.Compatibility.Interchange L Dh Dv)
  (hc : KernelFrame.Centrality.Central f Kh) (ht : Kernel.FramesTransverseTransport.Transverse g Kv Dh)

include hi hc ht in
/-- The genuine horizontal product is equivariant under the complete constructed quotient transport. -/
theorem horizontal_product {T : Over S} (x y u v : T ⟶ A) (z w : T ⟶ X)
    (hx : x ≫ f = u ≫ f) (hy : y ≫ f = v ≫ f) (hz : z ≫ g = w ≫ g)
    (U : T.left.Opens) (m : Γ(Line.Fibers.fiber L (lift x z), U)) (n : Γ(Line.Fibers.fiber L (lift y z), U)) :
    (CoordinateProductTranslations.productTo L Dh u v (u * v) w rfl).app U
      ((coordinateTotal f g L Dh Dv Kh Kv x u z w hx hz).app U m)
      ((coordinateTotal f g L Dh Dv Kh Kv y v z w hy hz).app U n) =
    (coordinateTotal f g L Dh Dv Kh Kv (x * y) (u * v) z w
      (Kernel.DifferenceProduct.product_images f x u y v hx hy) hz).app U
      ((CoordinateProductTranslations.productTo L Dh x y (x * y) z rfl).app U m n) := by
  change (CoordinateProductTranslations.productTo L Dh u v (u * v) w rfl).app U
      ((Biextension.AxisData.vertical g L Dv Kv _ _ (QuotientTransverseProduct.liftedVertical g u z w hz)).app U
        ((Biextension.AxisData.horizontal f L Dh Kh _ _ (QuotientHorizontalProduct.liftedHorizontal f x u z hx)).app U m))
      ((Biextension.AxisData.vertical g L Dv Kv _ _ (QuotientTransverseProduct.liftedVertical g v z w hz)).app U
        ((Biextension.AxisData.horizontal f L Dh Kh _ _ (QuotientHorizontalProduct.liftedHorizontal f y v z hy)).app U n)) =
    (Biextension.AxisData.vertical g L Dv Kv _ _ (QuotientTransverseProduct.liftedVertical g (u * v) z w hz)).app U
      ((Biextension.AxisData.horizontal f L Dh Kh _ _ (QuotientHorizontalProduct.liftedHorizontal f (x * y) (u * v) z
        (Kernel.DifferenceProduct.product_images f x u y v hx hy))).app U
        ((CoordinateProductTranslations.productTo L Dh x y (x * y) z rfl).app U m n))
  rw [QuotientTransverseProduct.horizontal_product L Dh Dv hi g Kv ht u v z w hz,
    QuotientHorizontalProduct.horizontal_product f L Dh Kh hc x y u v z hx hy]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.QuotientProductComposition
