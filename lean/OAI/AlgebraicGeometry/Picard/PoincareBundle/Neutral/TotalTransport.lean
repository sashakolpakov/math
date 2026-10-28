import OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.AxisTransport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.QuotientProductComposition
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.PointNormalForm

/-! # Total Transport -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.TotalTransport

noncomputable section

/-!
# The full actual quotient transport preserves the horizontal neutral unit
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.AxisData OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization
open OAI.AlgebraicGeometry.Picard.PoincareBundle.QuotientProductComposition OAI.AlgebraicGeometry.Picard.PoincareBundle.QuotientHorizontalProduct OAI.AlgebraicGeometry.Picard.PoincareBundle.QuotientTransverseProduct

variable {S : Scheme.{u}} {A B X Y : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (f : A ⟶ B) (g : X ⟶ Y) [IsMonHom f] [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh) (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)

/-- On the horizontal neutral axis the full quotient transport is the actual vertical quotient transport. -/
theorem total_eq_vertical {T : Over S} (z w : T ⟶ X) (hz : z ≫ g = w ≫ g) :
    RectangularTransport.total f g (Geometric.KernelLinearization.overModulePullbacks S) L.sheaf (Biextension.AxisData.toAxisData f g L Dh Dv Kh Kv)
      (lift (1 : T ⟶ A) z) (lift (1 : T ⟶ A) w) (QuotientProductComposition.product_images f g 1 1 z w rfl hz) =
    Biextension.AxisData.vertical g L Dv Kv (lift (1 : T ⟶ A) z) (lift (1 : T ⟶ A) w) (QuotientTransverseProduct.liftedVertical g 1 z w hz) := by
  have hh : Biextension.AxisData.horizontal f L Dh Kh (lift (1 : T ⟶ A) z) (lift (1 : T ⟶ A) z)
      (QuotientHorizontalProduct.liftedHorizontal f 1 1 z rfl) = 𝟙 _ :=
    (Biextension.AxisData.toAxisData f g L Dh Dv Kh Kv).horizontal_self _ (QuotientHorizontalProduct.liftedHorizontal f 1 1 z rfl)
  exact (QuotientProductComposition.native_total f g L Dh Dv Kh Kv 1 1 z w rfl hz).trans
    ((congrArg (fun a => a ≫ Biextension.AxisData.vertical g L Dv Kv (lift (1 : T ⟶ A) z) (lift (1 : T ⟶ A) w)
      (QuotientTransverseProduct.liftedVertical g 1 z w hz)) hh).trans (Category.id_comp _))

variable (hi : Biextension.Compatibility.Interchange L Dh Dv)
  (ht : Kernel.FramesTransverseTransport.Transverse g Kv Dh)

include hi ht in
/-- The constructed full quotient transport preserves the actual normalized horizontal unit on every test scheme. -/
theorem total_unit {T : Over S} (z w : T ⟶ X) (hz : z ≫ g = w ≫ g) :
    (Dh.unitFrame (lift (1 : T ⟶ A) z) (lift_fst _ _)).hom ≫
      RectangularTransport.total f g (Geometric.KernelLinearization.overModulePullbacks S) L.sheaf (Biextension.AxisData.toAxisData f g L Dh Dv Kh Kv)
        (lift (1 : T ⟶ A) z) (lift (1 : T ⟶ A) w) (QuotientProductComposition.product_images f g 1 1 z w rfl hz) =
    (Dh.unitFrame (lift (1 : T ⟶ A) w) (lift_fst _ _)).hom := by
  rw [total_eq_vertical f g L Dh Dv Kh Kv z w hz]
  exact AxisTransport.quotient_unit g L Dh Dv Kv hi ht z w hz

include hi ht in
/-- Full quotient transport preserves the normalized unit between arbitrary actual neutral-axis test points. -/
theorem total_unit_neutral {T : Over S} (a b : T ⟶ A ⊗ X)
    (ha : a ≫ fst A X = 1) (hb : b ≫ fst A X = 1)
    (h : a ≫ (f ⊗ₘ g) = b ≫ (f ⊗ₘ g)) :
    (Dh.unitFrame a ha).hom ≫
      RectangularTransport.total f g (Geometric.KernelLinearization.overModulePullbacks S) L.sheaf (Biextension.AxisData.toAxisData f g L Dh Dv Kh Kv) a b h =
    (Dh.unitFrame b hb).hom := by
  obtain ⟨z, rfl⟩ := PointNormalForm.neutral_normalForm a ha
  obtain ⟨w, rfl⟩ := PointNormalForm.neutral_normalForm b hb
  exact total_unit f g L Dh Dv Kh Kv hi ht z w (Product.PointNormalForm.images_snd f g 1 1 z w h)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.TotalTransport
