import OAI.AlgebraicGeometry.Picard.PoincareBundle.TransverseFrameUnits
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateQuotientTransport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.QuotientTransverseProduct

/-! # Axis Transport -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.AxisTransport

noncomputable section

/-!
# Actual quotient transport preserves the normalized unit on the neutral axis
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Pair
open OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateTransverseTranslations OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.AxisData OAI.AlgebraicGeometry.Picard.PoincareBundle.QuotientTransverseProduct

variable {S : Scheme.{u}} {A X Y : Over S} [GrpObj A] [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (g : X ⟶ Y) [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)
  (hi : Biextension.Compatibility.Interchange L Dh Dv)
  (ht : Kernel.FramesTransverseTransport.Transverse g Kv Dh)

include hi ht in
omit [IsCommMonObj X] in
/-- Actual vertical kernel translation carries the first neutral unit frame to the second. -/
theorem translate_unit {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject g) (z w : T ⟶ X)
    (hk : (k ≫ Kernel.Scheme.kernelInclusion g) * z = w) :
    (Dh.unitFrame (lift (1 : T ⟶ A) z) (lift_fst _ _)).hom ≫
      CoordinateTransverseTranslations.verticalTranslateTo L Dv g Kv k z w (1 : T ⟶ A) hk =
    (Dh.unitFrame (lift (1 : T ⟶ A) w) (lift_fst _ _)).hom := by
  have hf := TransverseFrameUnits.vertical_frame_eq_horizontal_unit g L Dh Dv Kv ht k
    (lift (1 : T ⟶ A) (k ≫ Kernel.Scheme.kernelInclusion g)) (lift_snd _ _).symm (lift_fst _ _)
  apply Line.FrameUnits.unit_hom_ext
  intro U
  change (CoordinateTransverseTranslations.verticalTranslateTo L Dv g Kv k z w (1 : T ⟶ A) hk).app U
    ((Dh.unitFrame (lift (1 : T ⟶ A) z) (lift_fst _ _)).hom.app U (1 : Γ(T.left, U))) = _
  dsimp only [CoordinateTransverseTranslations.verticalTranslateTo]
  rw [Bilinear.Contraction.contractLeft_app, hf]
  exact InterchangeNeutralFrames.horizontal_units_vertical_product L Dh Dv hi
    (lift (1 : T ⟶ A) (k ≫ Kernel.Scheme.kernelInclusion g)) (lift (1 : T ⟶ A) z) (lift (1 : T ⟶ A) w)
    (lift_fst _ _) (lift_fst _ _) (lift_fst _ _) (CoordinateTransverseTranslations.verticalRel _ _ _ _ hk) U

include hi ht in
/-- The genuine vertical quotient map preserves the horizontal unit on every equal-image pair. -/
theorem quotient_unit {T : Over S} (z w : T ⟶ X) (hz : z ≫ g = w ≫ g) :
    (Dh.unitFrame (lift (1 : T ⟶ A) z) (lift_fst _ _)).hom ≫
      Biextension.AxisData.vertical g L Dv Kv (lift (1 : T ⟶ A) z) (lift (1 : T ⟶ A) w) (QuotientTransverseProduct.liftedVertical g 1 z w hz) =
    (Dh.unitFrame (lift (1 : T ⟶ A) w) (lift_fst _ _)).hom := by
  rw [CoordinateQuotientTransport.vertical_eq g L Dv Kv (Kernel.Pair.pointDifference g z w hz) z w 1 _
    (QuotientHorizontalProduct.difference_left_translation g z w hz)]
  exact translate_unit g L Dh Dv Kv hi ht _ z w _

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.AxisTransport
