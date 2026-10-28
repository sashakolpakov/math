import OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateTransverseTranslations

/-! # Transverse Target Translations -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.TransverseTargetTranslations

noncomputable section

/-!
# Transverse product equivariance with arbitrary specified translation targets
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesTransverseTransport
open OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateProductTranslations OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateTransverseTranslations

variable {S : Scheme.{u}} {A B X Y : Over S} [GrpObj A] [GrpObj X]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (hi : Biextension.Compatibility.Interchange L Dh Dv)

section VerticalTranslations

variable [GrpObj Y] (g : X ⟶ Y) [IsMonHom g] (Fv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)
  (ht : Kernel.FramesTransverseTransport.Transverse g Fv Dh)

include hi ht in
/-- Horizontal products commute with vertical kernel translation to any specified target coordinate. -/
theorem horizontal_product_to {T : Over S} (l : T ⟶ Kernel.Scheme.kernelObject g) (x y : T ⟶ A) (z w : T ⟶ X)
    (hl : (l ≫ Kernel.Scheme.kernelInclusion g) * z = w) (U : T.left.Opens)
    (m : Γ(Line.Fibers.fiber L (lift x z), U)) (n : Γ(Line.Fibers.fiber L (lift y z), U)) :
    (CoordinateProductTranslations.productTo L Dh x y (x * y) w rfl).app U
      ((CoordinateTransverseTranslations.verticalTranslateTo L Dv g Fv l z w x hl).app U m)
      ((CoordinateTransverseTranslations.verticalTranslateTo L Dv g Fv l z w y hl).app U n) =
    (CoordinateTransverseTranslations.verticalTranslateTo L Dv g Fv l z w (x * y) hl).app U
      ((CoordinateProductTranslations.productTo L Dh x y (x * y) z rfl).app U m n) := by
  subst w
  exact CoordinateTransverseTranslations.horizontal_product L Dh Dv hi g Fv ht l x y z U m n

end VerticalTranslations

variable [GrpObj B] (f : A ⟶ B) [IsMonHom f] (Fh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh)
  (ht : Kernel.FramesTransverseTransport.Transverse f Fh Dv)

include hi ht in
/-- Vertical products commute with horizontal kernel translation to any specified target coordinate. -/
theorem vertical_product_to {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (x y : T ⟶ A) (z w : T ⟶ X)
    (hk : (k ≫ Kernel.Scheme.kernelInclusion f) * x = y) (U : T.left.Opens)
    (m : Γ(Line.Fibers.fiber L (lift x z), U)) (n : Γ(Line.Fibers.fiber L (lift x w), U)) :
    (CoordinateTransverseTranslations.verticalProductTo L Dv z w (z * w) y rfl).app U
      ((CoordinateProductTranslations.translateTo L Dh f Fh k x y z hk).app U m) ((CoordinateProductTranslations.translateTo L Dh f Fh k x y w hk).app U n) =
    (CoordinateProductTranslations.translateTo L Dh f Fh k x y (z * w) hk).app U ((CoordinateTransverseTranslations.verticalProductTo L Dv z w (z * w) x rfl).app U m n) := by
  subst y
  exact CoordinateTransverseTranslations.vertical_product L Dh Dv hi f Fh ht k x z w U m n

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.TransverseTargetTranslations
