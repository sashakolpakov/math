import OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateProductTranslations
import OAI.AlgebraicGeometry.Picard.PoincareBundle.TransverseProductEquivariance

/-! # Coordinate Transverse Translations -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateTransverseTranslations

noncomputable section

/-!
# Transverse product equivariance on the actual lifted scheme coordinates
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction
open OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateProductTranslations OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesTransverseTransport

variable {S : Scheme.{u}} {A B X Y : Over S} [GrpObj A] [GrpObj X]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (hi : Biextension.Compatibility.Interchange L Dh Dv)

omit [GrpObj A] in
/-- Actual lifted coordinates also give the vertical product relation. -/
theorem verticalRel {T : Over S} (a b c : T ⟶ X) (x : T ⟶ A) (h : a * b = c) :
    FiberwiseMultiplication.ProductRel (snd A X) (fst A X) (lift x a) (lift x b) (lift x c) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [lift_snd] using h
  · simp only [lift_fst]
  · simp only [lift_fst]

/-- The actual second-coordinate product at specified group coordinates. -/
def verticalProductTo {T : Over S} (a b c : T ⟶ X) (x : T ⟶ A) (h : a * b = c) :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Line.Fibers.fiber L (lift x a)) (Line.Fibers.fiber L (lift x b)) (Line.Fibers.fiber L (lift x c)) :=
  Dv.product _ _ _ (verticalRel a b c x h)

section VerticalTranslations

variable [GrpObj Y] (g : X ⟶ Y) [IsMonHom g] (Fv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)

/-- The genuine second-coordinate kernel translation inserts its actual normalized kernel frame. -/
def verticalTranslateTo {T : Over S} (l : T ⟶ Kernel.Scheme.kernelObject g) (a b : T ⟶ X) (x : T ⟶ A)
    (h : (l ≫ Kernel.Scheme.kernelInclusion g) * a = b) : Line.Fibers.fiber L (lift x a) ⟶ Line.Fibers.fiber L (lift x b) :=
  Bilinear.Contraction.contractLeft (verticalProductTo L Dv (l ≫ Kernel.Scheme.kernelInclusion g) a b x h)
    (Fv.frame l (lift x (l ≫ Kernel.Scheme.kernelInclusion g)) (lift_snd _ _).symm).hom

variable (ht : Kernel.FramesTransverseTransport.Transverse g Fv Dh)

include hi ht in
/-- The horizontal product commutes with vertical kernel translations at the actual canonical coordinates. -/
theorem horizontal_product {T : Over S} (l : T ⟶ Kernel.Scheme.kernelObject g) (x y : T ⟶ A) (z : T ⟶ X)
    (U : T.left.Opens) (m : Γ(Line.Fibers.fiber L (lift x z), U)) (n : Γ(Line.Fibers.fiber L (lift y z), U)) :
    (CoordinateProductTranslations.productTo L Dh x y (x * y) ((l ≫ Kernel.Scheme.kernelInclusion g) * z) rfl).app U
      ((verticalTranslateTo L Dv g Fv l z ((l ≫ Kernel.Scheme.kernelInclusion g) * z) x rfl).app U m)
      ((verticalTranslateTo L Dv g Fv l z ((l ≫ Kernel.Scheme.kernelInclusion g) * z) y rfl).app U n) =
    (verticalTranslateTo L Dv g Fv l z ((l ≫ Kernel.Scheme.kernelInclusion g) * z) (x * y) rfl).app U
      ((CoordinateProductTranslations.productTo L Dh x y (x * y) z rfl).app U m n) := by
  dsimp only [verticalTranslateTo]
  rw [Bilinear.Contraction.contractLeft_app, Bilinear.Contraction.contractLeft_app, Bilinear.Contraction.contractLeft_app]
  exact TransverseProductEquivariance.horizontal_product L Dh Dv hi
    (lift x (l ≫ Kernel.Scheme.kernelInclusion g)) (lift x z) (lift y (l ≫ Kernel.Scheme.kernelInclusion g)) (lift y z)
    (lift x ((l ≫ Kernel.Scheme.kernelInclusion g) * z)) (lift (x * y) (l ≫ Kernel.Scheme.kernelInclusion g))
    (lift (x * y) z) (lift y ((l ≫ Kernel.Scheme.kernelInclusion g) * z)) (lift (x * y) ((l ≫ Kernel.Scheme.kernelInclusion g) * z))
    (CoordinateProductTranslations.liftedRel _ _ _ _ rfl) (verticalRel _ _ _ _ rfl) (CoordinateProductTranslations.liftedRel _ _ _ _ rfl)
    (verticalRel _ _ _ _ rfl) (verticalRel _ _ _ _ rfl) (CoordinateProductTranslations.liftedRel _ _ _ _ rfl)
    g Fv ht l (lift_snd _ _).symm (lift_snd _ _).symm (lift_snd _ _).symm U m n

end VerticalTranslations

variable [GrpObj B] (f : A ⟶ B) [IsMonHom f] (Fh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh)
  (ht : Kernel.FramesTransverseTransport.Transverse f Fh Dv)

include hi ht in
/-- The vertical product commutes with horizontal kernel translations on the actual canonical coordinates. -/
theorem vertical_product {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (x : T ⟶ A) (z w : T ⟶ X)
    (U : T.left.Opens) (m : Γ(Line.Fibers.fiber L (lift x z), U)) (n : Γ(Line.Fibers.fiber L (lift x w), U)) :
    (verticalProductTo L Dv z w (z * w) ((k ≫ Kernel.Scheme.kernelInclusion f) * x) rfl).app U
      ((CoordinateProductTranslations.translateTo L Dh f Fh k x ((k ≫ Kernel.Scheme.kernelInclusion f) * x) z rfl).app U m)
      ((CoordinateProductTranslations.translateTo L Dh f Fh k x ((k ≫ Kernel.Scheme.kernelInclusion f) * x) w rfl).app U n) =
    (CoordinateProductTranslations.translateTo L Dh f Fh k x ((k ≫ Kernel.Scheme.kernelInclusion f) * x) (z * w) rfl).app U
      ((verticalProductTo L Dv z w (z * w) x rfl).app U m n) := by
  dsimp only [CoordinateProductTranslations.translateTo]
  rw [Bilinear.Contraction.contractLeft_app, Bilinear.Contraction.contractLeft_app, Bilinear.Contraction.contractLeft_app]
  exact TransverseProductEquivariance.vertical_product L Dh Dv hi
    (lift (k ≫ Kernel.Scheme.kernelInclusion f) z) (lift (k ≫ Kernel.Scheme.kernelInclusion f) w) (lift x z) (lift x w)
    (lift (k ≫ Kernel.Scheme.kernelInclusion f) (z * w)) (lift ((k ≫ Kernel.Scheme.kernelInclusion f) * x) z)
    (lift ((k ≫ Kernel.Scheme.kernelInclusion f) * x) w) (lift x (z * w)) (lift ((k ≫ Kernel.Scheme.kernelInclusion f) * x) (z * w))
    (CoordinateProductTranslations.liftedRel _ _ _ _ rfl) (verticalRel _ _ _ _ rfl) (CoordinateProductTranslations.liftedRel _ _ _ _ rfl)
    (verticalRel _ _ _ _ rfl) (verticalRel _ _ _ _ rfl) (CoordinateProductTranslations.liftedRel _ _ _ _ rfl)
    f Fh ht k (lift_fst _ _).symm (lift_fst _ _).symm (lift_fst _ _).symm U m n

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateTransverseTranslations
