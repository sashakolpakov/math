import OAI.AlgebraicGeometry.Picard.PoincareBundle.InterchangeNeutralFrames
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesTransverseTransport

/-! # Transverse Frame Units -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.TransverseFrameUnits

noncomputable section

/-!
# A transverse multiplicative kernel frame is the actual unit on the neutral axis
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ProductFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.InterchangeNeutralFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesTransverseTransport

variable {S : Scheme.{u}} {A X Y : Over S} [GrpObj A] [GrpObj X] [GrpObj Y]
  (g : X ⟶ Y) [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv) (ht : Kernel.FramesTransverseTransport.Transverse g Kv Dh)

include ht in
/-- The actual vertical kernel frame on a horizontally neutral point equals the horizontal unit frame. -/
theorem vertical_frame_eq_horizontal_unit {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject g) (a : T ⟶ A ⊗ X)
    (hk : k ≫ Kernel.Scheme.kernelInclusion g = a ≫ snd A X) (ha : a ≫ fst A X = 1) :
    Kv.frame k a hk = Dh.unitFrame a ha := by
  let h := InterchangeNeutralFrames.neutral_rel (fst A X) (snd A X) a ha
  exact Bilinear.ProductFrames.idempotent_frame_unique (Dh.product a a a h) (Kv.frame k a hk) (Dh.unitFrame a ha)
    (ht T k a a a hk hk hk h ⊤) (Dh.unit_left a a ha h ⊤ _)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.TransverseFrameUnits
