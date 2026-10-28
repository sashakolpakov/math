import OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateKernelTransport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.DifferenceProduct
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.QuotientCommutation

/-! # Coordinate Quotient Transport -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateQuotientTransport

noncomputable section

/-!
# The actual quotient-coordinate transport is the explicit canonical kernel translation
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Pair OAI.AlgebraicGeometry.Picard.PoincareBundle.RectangularCoordinates OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.AxisData
open OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateProductTranslations OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateTransverseTranslations OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateKernelTransport
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.QuotientCommutation

section Horizontal

variable {S : Scheme.{u}} {A B X : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f] (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (D : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (F : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f D)

/-- The constructed horizontal quotient transport agrees with any specified actual kernel translation. -/
theorem horizontal_eq {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (x y : T ⟶ A) (z : T ⟶ X)
    (h : RectangularCoordinates.Horizontal f (lift x z) (lift y z)) (hk : (k ≫ Kernel.Scheme.kernelInclusion f) * x = y) :
    Biextension.AxisData.horizontal f L D F (lift x z) (lift y z) h = CoordinateProductTranslations.translateTo L D f F k x y z hk := by
  have hxy : x ≫ f = y ≫ f := by simpa only [← Category.assoc, lift_fst] using h.1
  have hd : Kernel.Pair.pointDifference f (lift x z ≫ fst A X) (lift y z ≫ fst A X)
      (Biextension.AxisData.horizontalRelation f _ _ h).1 = k :=
    (Biextension.QuotientCommutation.pointDifference_congr f _ _ x y (Biextension.AxisData.horizontalRelation f _ _ h).1 hxy (lift_fst _ _) (lift_fst _ _)).trans
      (Kernel.DifferenceProduct.difference_of_translation f k x y hxy hk)
  have ht : (lift x z ≫ fst A X) * (k ≫ Kernel.Scheme.kernelInclusion f) = lift y z ≫ fst A X := by
    rw [lift_fst, lift_fst]
    exact (mul_comm _ _).trans hk
  exact (Biextension.QuotientCommutation.horizontal_eq_kernel f L D F _ _ h k hd ht).trans (CoordinateKernelTransport.horizontal_transport f L D F k x y z hk)

end Horizontal

variable {S : Scheme.{u}} {A X Y : Over S} [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (g : X ⟶ Y) [IsMonHom g] (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (D : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L) (F : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g D)

/-- The constructed vertical quotient transport agrees with the actual specified second-coordinate kernel translation. -/
theorem vertical_eq {T : Over S} (l : T ⟶ Kernel.Scheme.kernelObject g) (z w : T ⟶ X) (x : T ⟶ A)
    (h : RectangularCoordinates.Vertical g (lift x z) (lift x w)) (hl : (l ≫ Kernel.Scheme.kernelInclusion g) * z = w) :
    Biextension.AxisData.vertical g L D F (lift x z) (lift x w) h = CoordinateTransverseTranslations.verticalTranslateTo L D g F l z w x hl := by
  have hzw : z ≫ g = w ≫ g := by simpa only [← Category.assoc, lift_snd] using h.2
  have hd : Kernel.Pair.pointDifference g (lift x z ≫ snd A X) (lift x w ≫ snd A X)
      (Biextension.AxisData.verticalRelation g _ _ h).1 = l :=
    (Biextension.QuotientCommutation.pointDifference_congr g _ _ z w (Biextension.AxisData.verticalRelation g _ _ h).1 hzw (lift_snd _ _) (lift_snd _ _)).trans
      (Kernel.DifferenceProduct.difference_of_translation g l z w hzw hl)
  have ht : (lift x z ≫ snd A X) * (l ≫ Kernel.Scheme.kernelInclusion g) = lift x w ≫ snd A X := by
    rw [lift_snd, lift_snd]
    exact (mul_comm _ _).trans hl
  exact (Biextension.QuotientCommutation.vertical_eq_kernel g L D F _ _ h l hd ht).trans (CoordinateKernelTransport.vertical_transport g L D F l z w x hl)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateQuotientTransport
