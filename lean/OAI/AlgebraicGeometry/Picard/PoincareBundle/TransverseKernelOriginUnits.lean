import OAI.AlgebraicGeometry.Picard.PoincareBundle.SecondTransverseFrameUnits

/-! # Transverse Kernel Origin Units -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.TransverseKernelOriginUnits

noncomputable section

/-! A transverse kernel-frame system identifies the two origin units without an additional normalization hypothesis. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

attribute [local instance] Kernel.Scheme.kernelGroup

variable {S : Scheme.{u}} {A B X : Over S} [GrpObj A] [GrpObj B] [GrpObj X]
  (f : A ⟶ B) [IsMonHom f] (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (K : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh)
  (ht : Kernel.FramesTransverseTransport.Transverse f K Dv)

include ht

/-- The two actual units agree at any point neutral in both coordinates. -/
theorem unitFrames_eq {T : Over S} (a : T ⟶ A ⊗ X)
    (hh : a ≫ fst A X = 1) (hv : a ≫ snd A X = 1) : Dh.unitFrame a hh = Dv.unitFrame a hv := by
  have hk : (1 : T ⟶ Kernel.Scheme.kernelObject f) ≫ Kernel.Scheme.kernelInclusion f = a ≫ fst A X :=
    (MonObj.one_comp (Kernel.Scheme.kernelInclusion f)).trans hh.symm
  exact (K.unit a hh hk).symm.trans
    (SecondTransverseFrameUnits.horizontal_frame_eq_vertical_unit f L Dh Dv K ht 1 a hk hv)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.TransverseKernelOriginUnits
