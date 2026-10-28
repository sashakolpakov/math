import OAI.AlgebraicGeometry.Picard.PoincareBundle.TransverseFrameUnits

/-! # Second Transverse Frame Units -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.SecondTransverseFrameUnits

noncomputable section

/-!
# The first-coordinate kernel frame is the actual second-coordinate unit on its neutral axis
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ProductFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.InterchangeNeutralFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesTransverseTransport

variable {S : Scheme.{u}} {A B X : Over S} [GrpObj A] [GrpObj B] [GrpObj X]
  (f : A ⟶ B) [IsMonHom f]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh) (ht : Kernel.FramesTransverseTransport.Transverse f Kh Dv)

include ht in
/-- On a vertically neutral point the actual horizontal kernel frame equals the vertical unit frame. -/
theorem horizontal_frame_eq_vertical_unit {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (a : T ⟶ A ⊗ X)
    (hk : k ≫ Kernel.Scheme.kernelInclusion f = a ≫ fst A X) (ha : a ≫ snd A X = 1) :
    Kh.frame k a hk = Dv.unitFrame a ha := by
  let h := InterchangeNeutralFrames.neutral_rel (snd A X) (fst A X) a ha
  exact Bilinear.ProductFrames.idempotent_frame_unique (Dv.product a a a h) (Kh.frame k a hk) (Dv.unitFrame a ha)
    (ht T k a a a hk hk hk h ⊤) (Dv.unit_left a a ha h ⊤ _)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.SecondTransverseFrameUnits
