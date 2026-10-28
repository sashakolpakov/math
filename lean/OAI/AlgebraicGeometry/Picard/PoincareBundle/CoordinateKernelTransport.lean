import OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateTransverseTranslations
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.KernelRectangle

/-! # Coordinate Kernel Transport -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateKernelTransport

noncomputable section

/-!
# The actual kernel-action sheaf maps are the explicit coordinate translations
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseKernelCoordinates OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.AxisData
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.KernelRectangle OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateProductTranslations OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateTransverseTranslations

/-- Equal actual kernel insertion points give the same contracted sheaf map, including their dependent product proofs. -/
theorem contraction_point_eq {S : Scheme.{u}} {E A B X : Over S} [GrpObj A] [GrpObj B]
    {p : E ⟶ A} {r : E ⟶ X} (f : A ⟶ B) [IsMonHom f]
    (L : Line.Bundles.LineBundle E.left) (D : FiberwiseMultiplication.Multiplication p r L) (F : FiberwiseMultiplication.KernelFrames p r L f D)
    {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (x y a b : T ⟶ E) (hab : a = b)
    (hax : FiberwiseMultiplication.ProductRel p r a x y) (hbx : FiberwiseMultiplication.ProductRel p r b x y)
    (ha : k ≫ Kernel.Scheme.kernelInclusion f = a ≫ p) (hb : k ≫ Kernel.Scheme.kernelInclusion f = b ≫ p) :
    Bilinear.Contraction.contractLeft (D.product a x y hax) (F.frame k a ha).hom =
      Bilinear.Contraction.contractLeft (D.product b x y hbx) (F.frame k b hb).hom := by
  cases hab
  rfl

section Horizontal

variable {S : Scheme.{u}} {A B X : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f]

omit [GrpObj A] [IsCommMonObj A] [IsMonHom f] in
/-- The actual first-coordinate replacement is the canonical lift of the included kernel point. -/
theorem horizontal_kernelPoint {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (x : T ⟶ A) (z : T ⟶ X) :
    FiberwiseKernelCoordinates.kernelPoint f Biextension.AxisData.replaceFirst k (lift x z) = lift (k ≫ Kernel.Scheme.kernelInclusion f) z := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Biextension.KernelRectangle.horizontalPoint_fst, lift_fst]
  · rw [Biextension.KernelRectangle.horizontalPoint_snd, lift_snd, lift_snd]

variable (L : Line.Bundles.LineBundle (A ⊗ X).left) (D : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L)
  (F : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f D)

/-- The constructed native first-coordinate kernel transport is exactly contraction at the canonical coordinates. -/
theorem horizontal_transport {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (x y : T ⟶ A) (z : T ⟶ X)
    (h : (k ≫ Kernel.Scheme.kernelInclusion f) * x = y) :
    FiberwiseKernelTransport.transport (fst A X) (snd A X) f Biextension.AxisData.replaceFirst Biextension.AxisData.replaceFirst_group Biextension.AxisData.replaceFirst_base
      L D F (lift x z) (lift y z) k
      (by rw [lift_fst, lift_fst]; exact (mul_comm _ _).trans h) (by rw [lift_snd, lift_snd]) =
      CoordinateProductTranslations.translateTo L D f F k x y z h := by
  unfold FiberwiseKernelTransport.transport CoordinateProductTranslations.translateTo CoordinateProductTranslations.productTo
  exact contraction_point_eq f L D F k _ _ _ _ (horizontal_kernelPoint f k x z) _ _ _ _

end Horizontal

variable {S : Scheme.{u}} {A X Y : Over S} [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (g : X ⟶ Y) [IsMonHom g]

omit [GrpObj X] [IsCommMonObj X] [IsMonHom g] in
/-- The second-coordinate replacement is the canonical lift of the included kernel point. -/
theorem vertical_kernelPoint {T : Over S} (l : T ⟶ Kernel.Scheme.kernelObject g) (x : T ⟶ A) (z : T ⟶ X) :
    FiberwiseKernelCoordinates.kernelPoint g Biextension.AxisData.replaceSecond l (lift x z) = lift x (l ≫ Kernel.Scheme.kernelInclusion g) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Biextension.KernelRectangle.verticalPoint_fst, lift_fst, lift_fst]
  · rw [Biextension.KernelRectangle.verticalPoint_snd, lift_snd]

variable (L : Line.Bundles.LineBundle (A ⊗ X).left) (D : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (F : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g D)

/-- The native second-coordinate kernel transport is the explicit canonical vertical translation. -/
theorem vertical_transport {T : Over S} (l : T ⟶ Kernel.Scheme.kernelObject g) (z w : T ⟶ X) (x : T ⟶ A)
    (h : (l ≫ Kernel.Scheme.kernelInclusion g) * z = w) :
    FiberwiseKernelTransport.transport (snd A X) (fst A X) g Biextension.AxisData.replaceSecond Biextension.AxisData.replaceSecond_group Biextension.AxisData.replaceSecond_base
      L D F (lift x z) (lift x w) l
      (by rw [lift_snd, lift_snd]; exact (mul_comm _ _).trans h) (by rw [lift_fst, lift_fst]) =
      CoordinateTransverseTranslations.verticalTranslateTo L D g F l z w x h := by
  unfold FiberwiseKernelTransport.transport CoordinateTransverseTranslations.verticalTranslateTo CoordinateTransverseTranslations.verticalProductTo
  exact contraction_point_eq g L D F l _ _ _ _ (vertical_kernelPoint g l x z) _ _ _ _

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateKernelTransport
