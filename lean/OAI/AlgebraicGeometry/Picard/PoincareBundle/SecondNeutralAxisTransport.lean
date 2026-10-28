import OAI.AlgebraicGeometry.Picard.PoincareBundle.SecondTransverseFrameUnits
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateQuotientTransport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.QuotientHorizontalProduct

/-! # Second Neutral Axis Transport -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.SecondNeutralAxisTransport

noncomputable section

/-!
# Actual first-coordinate quotient transport preserves the second neutral unit
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Pair
open OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateProductTranslations OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.AxisData OAI.AlgebraicGeometry.Picard.PoincareBundle.QuotientHorizontalProduct

variable {S : Scheme.{u}} {A B X : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [GrpObj X]
  (f : A ⟶ B) [IsMonHom f]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh)
  (hi : Biextension.Compatibility.Interchange L Dh Dv)
  (ht : Kernel.FramesTransverseTransport.Transverse f Kh Dv)

include hi ht in
omit [IsCommMonObj A] in
/-- Actual horizontal kernel translation carries the vertical unit frame to the vertical unit frame. -/
theorem translate_unit {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (x y : T ⟶ A)
    (hk : (k ≫ Kernel.Scheme.kernelInclusion f) * x = y) :
    (Dv.unitFrame (lift x (1 : T ⟶ X)) (lift_snd _ _)).hom ≫
      CoordinateProductTranslations.translateTo L Dh f Kh k x y (1 : T ⟶ X) hk =
    (Dv.unitFrame (lift y (1 : T ⟶ X)) (lift_snd _ _)).hom := by
  have hf := SecondTransverseFrameUnits.horizontal_frame_eq_vertical_unit f L Dh Dv Kh ht k
    (lift (k ≫ Kernel.Scheme.kernelInclusion f) (1 : T ⟶ X)) (lift_fst _ _).symm (lift_snd _ _)
  apply Line.FrameUnits.unit_hom_ext
  intro U
  change (CoordinateProductTranslations.translateTo L Dh f Kh k x y (1 : T ⟶ X) hk).app U
    ((Dv.unitFrame (lift x (1 : T ⟶ X)) (lift_snd _ _)).hom.app U (1 : Γ(T.left, U))) = _
  dsimp only [CoordinateProductTranslations.translateTo]
  rw [Bilinear.Contraction.contractLeft_app, hf]
  exact InterchangeNeutralFrames.vertical_units_horizontal_product L Dh Dv hi
    (lift (k ≫ Kernel.Scheme.kernelInclusion f) (1 : T ⟶ X)) (lift x (1 : T ⟶ X)) (lift y (1 : T ⟶ X))
    (lift_snd _ _) (lift_snd _ _) (lift_snd _ _) (CoordinateProductTranslations.liftedRel _ _ _ _ hk) U

include hi ht in
/-- The genuine horizontal quotient map preserves the vertical unit on every equal-image pair. -/
theorem quotient_unit {T : Over S} (x y : T ⟶ A) (hx : x ≫ f = y ≫ f) :
    (Dv.unitFrame (lift x (1 : T ⟶ X)) (lift_snd _ _)).hom ≫
      Biextension.AxisData.horizontal f L Dh Kh (lift x (1 : T ⟶ X)) (lift y (1 : T ⟶ X)) (QuotientHorizontalProduct.liftedHorizontal f x y 1 hx) =
    (Dv.unitFrame (lift y (1 : T ⟶ X)) (lift_snd _ _)).hom := by
  rw [CoordinateQuotientTransport.horizontal_eq f L Dh Kh (Kernel.Pair.pointDifference f x y hx) x y 1 _
    (QuotientHorizontalProduct.difference_left_translation f x y hx)]
  exact translate_unit f L Dh Dv Kh hi ht _ x y _

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.SecondNeutralAxisTransport
