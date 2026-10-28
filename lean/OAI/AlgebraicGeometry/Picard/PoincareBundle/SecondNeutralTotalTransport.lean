import OAI.AlgebraicGeometry.Picard.PoincareBundle.SecondNeutralAxisTransport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.NeutralPointNormalForm
import OAI.AlgebraicGeometry.Picard.PoincareBundle.QuotientProductComposition

/-! # Second Neutral Total Transport -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.SecondNeutralTotalTransport

noncomputable section

/-! # Full actual quotient transport preserves the vertical neutral unit -/

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

/-- On the vertical neutral axis the full transport is the actual horizontal quotient transport. -/
theorem total_eq_horizontal {T : Over S} (x y : T ⟶ A) (hx : x ≫ f = y ≫ f) :
    RectangularTransport.total f g (Geometric.KernelLinearization.overModulePullbacks S) L.sheaf (Biextension.AxisData.toAxisData f g L Dh Dv Kh Kv)
      (lift x (1 : T ⟶ X)) (lift y (1 : T ⟶ X)) (QuotientProductComposition.product_images f g x y 1 1 hx rfl) =
    Biextension.AxisData.horizontal f L Dh Kh (lift x (1 : T ⟶ X)) (lift y (1 : T ⟶ X)) (QuotientHorizontalProduct.liftedHorizontal f x y 1 hx) := by
  have hv : Biextension.AxisData.vertical g L Dv Kv (lift y (1 : T ⟶ X)) (lift y (1 : T ⟶ X))
      (QuotientTransverseProduct.liftedVertical g y 1 1 rfl) = 𝟙 _ :=
    (Biextension.AxisData.toAxisData f g L Dh Dv Kh Kv).vertical_self _ (QuotientTransverseProduct.liftedVertical g y 1 1 rfl)
  exact (QuotientProductComposition.native_total f g L Dh Dv Kh Kv x y 1 1 hx rfl).trans
    ((congrArg (fun a => Biextension.AxisData.horizontal f L Dh Kh (lift x (1 : T ⟶ X)) (lift y (1 : T ⟶ X))
      (QuotientHorizontalProduct.liftedHorizontal f x y 1 hx) ≫ a) hv).trans (Category.comp_id _))

variable (hi : Biextension.Compatibility.Interchange L Dh Dv)
  (ht : Kernel.FramesTransverseTransport.Transverse f Kh Dv)

include hi ht in
/-- Full quotient transport preserves the actual vertical neutral unit between canonical test points. -/
theorem total_unit {T : Over S} (x y : T ⟶ A) (hx : x ≫ f = y ≫ f) :
    (Dv.unitFrame (lift x (1 : T ⟶ X)) (lift_snd _ _)).hom ≫
      RectangularTransport.total f g (Geometric.KernelLinearization.overModulePullbacks S) L.sheaf (Biextension.AxisData.toAxisData f g L Dh Dv Kh Kv)
        (lift x (1 : T ⟶ X)) (lift y (1 : T ⟶ X)) (QuotientProductComposition.product_images f g x y 1 1 hx rfl) =
    (Dv.unitFrame (lift y (1 : T ⟶ X)) (lift_snd _ _)).hom := by
  rw [total_eq_horizontal f g L Dh Dv Kh Kv x y hx]
  exact SecondNeutralAxisTransport.quotient_unit f L Dh Dv Kh hi ht x y hx

include hi ht in
/-- Full quotient transport preserves the unit between arbitrary actual second-neutral test points. -/
theorem total_unit_neutral {T : Over S} (a b : T ⟶ A ⊗ X)
    (ha : a ≫ snd A X = 1) (hb : b ≫ snd A X = 1) (h : a ≫ (f ⊗ₘ g) = b ≫ (f ⊗ₘ g)) :
    (Dv.unitFrame a ha).hom ≫
      RectangularTransport.total f g (Geometric.KernelLinearization.overModulePullbacks S) L.sheaf (Biextension.AxisData.toAxisData f g L Dh Dv Kh Kv) a b h =
    (Dv.unitFrame b hb).hom := by
  obtain ⟨x, rfl⟩ := NeutralPointNormalForm.Second.neutral_normalForm a ha
  obtain ⟨y, rfl⟩ := NeutralPointNormalForm.Second.neutral_normalForm b hb
  exact total_unit f g L Dh Dv Kh Kv hi ht x y (Product.PointNormalForm.images_fst f g x y 1 1 h)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.SecondNeutralTotalTransport
