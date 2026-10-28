import OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.Global
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.FamilyFrameUniqueness
import OAI.AlgebraicGeometry.Picard.PoincareBundle.PullSectionEquality

/-! # Rigidity -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.Rigidity

noncomputable section

/-! Proper connected geometry uniquely determines a transverse natural kernel-frame system. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Bundles OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.Global

variable {k : Type u} [Field k] {A B X : Over (Spec (.of k))}
  [GrpObj A] [GrpObj B] [GrpObj X]
  [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
  (f : A ⟶ B) [IsMonHom f] [IsAffine (Kernel.Scheme.kernelObject f).left]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (K J : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh)
  (hK : Kernel.FramesTransverseTransport.Transverse f K Dv)
  (hJ : Kernel.FramesTransverseTransport.Transverse f J Dv)

include hK hJ

/-- The zero-axis product law fixes the actual global subgroup-product frame uniquely. -/
theorem globalFrame_eq : Global.globalFrame f L Dh K = Global.globalFrame f L Dh J := by
  apply Affine.FamilyFrameUniqueness.Family.iso_eq_of_zero X (Kernel.Scheme.kernelObject f)
    (Line.Bundles.LineBundle.trivial (Kernel.Scheme.kernelObject f ⊗ X).left) (L.pullback (Global.universalPoint f).left)
  apply PullSectionEquality.pullback_map_eq L
    (lift (𝟙 (Kernel.Scheme.kernelObject f)) (1 : Kernel.Scheme.kernelObject f ⟶ X)) (Global.universalPoint f)
    (lift (Kernel.Scheme.kernelInclusion f) (1 : Kernel.Scheme.kernelObject f ⟶ X)) (by simp [Global.universalPoint])
  exact (Global.globalFrame_zero f L Dh K Dv hK).trans (Global.globalFrame_zero f L Dh J Dv hJ).symm

/-- Every actual test-scheme kernel frame is uniquely determined by naturality and transversality. -/
theorem frame_eq {T : Over (Spec (.of k))} (x : T ⟶ Kernel.Scheme.kernelObject f) (a : T ⟶ A ⊗ X)
    (ha : x ≫ Kernel.Scheme.kernelInclusion f = a ≫ fst A X) : K.frame x a ha = J.frame x a ha := by
  apply Iso.ext
  rw [← Global.globalFrame_natural f L Dh K x a ha, ← Global.globalFrame_natural f L Dh J x a ha,
    globalFrame_eq f L Dh Dv K J hK hJ]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.Rigidity
