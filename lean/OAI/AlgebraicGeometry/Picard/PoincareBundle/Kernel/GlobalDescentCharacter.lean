import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.GlobalFrameProducts
import OAI.AlgebraicGeometry.Picard.PoincareBundle.ConcreteKernelPairing

/-! # Global Descent Character -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.GlobalDescentCharacter

noncomputable section

/-! The genuine native character of the first-kernel parameter family is the inverse of its original full kernel pairing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.Global
open OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalVerticalDescentCharacter OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.KernelRectangle

variable {S : Scheme.{u}} {A B X Y : Over S} [GrpObj A] [GrpObj B] [GrpObj X] [GrpObj Y]
  (f : A ⟶ B) [IsMonHom f] (g : X ⟶ Y) [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh) (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)

/-- Any actual point with the two included kernel coordinates evaluates the same original pairing. -/
theorem value_at {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (l : T ⟶ Kernel.Scheme.kernelObject g) (c : T ⟶ A ⊗ X)
    (hk : k ≫ Kernel.Scheme.kernelInclusion f = c ≫ fst A X) (hl : l ≫ Kernel.Scheme.kernelInclusion g = c ≫ snd A X) :
    ConcreteKernelPairing.Concrete.value f g L Dh Dv Kh Kv k l =
      Biextension.Compatibility.kernelObstruction L Dh Dv f g Kh Kv k l c hk hl := by
  have hc : Biextension.KernelRectangle.crossPoint f g k l = c := by
    apply CartesianMonoidalCategory.hom_ext
    · exact (Biextension.KernelRectangle.crossPoint_fst f g k l).trans hk
    · exact (Biextension.KernelRectangle.crossPoint_snd f g k l).trans hl
  subst c
  rfl

/-- The global parameter-frame obstruction is the original pairing on the two full scheme-theoretic kernels. -/
theorem frame_ratio {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (l : T ⟶ Kernel.Scheme.kernelObject g) :
    Line.FrameUnits.frameRatio
      (GlobalVerticalDescentCharacter.frame (L.pullback (KernelFrame.Global.universalPoint f).left) (KernelFrame.Global.globalFrame f L Dh Kh).symm (lift k (l ≫ Kernel.Scheme.kernelInclusion g)))
      ((Vertical.ParameterKernelFrames.frames (Kernel.Scheme.kernelInclusion f) g L Dv Kv).frame l
        (lift k (l ≫ Kernel.Scheme.kernelInclusion g)) (lift_snd _ _).symm) =
    ConcreteKernelPairing.Concrete.value f g L Dh Dv Kh Kv k l := by
  let c := lift k (l ≫ Kernel.Scheme.kernelInclusion g)
  have hk : k ≫ Kernel.Scheme.kernelInclusion f = (c ≫ KernelFrame.Global.universalPoint f) ≫ fst A X := by simp [c, KernelFrame.Global.universalPoint]
  have hl : l ≫ Kernel.Scheme.kernelInclusion g = (c ≫ KernelFrame.Global.universalPoint f) ≫ snd A X := by simp [c, KernelFrame.Global.universalPoint]
  change Line.FrameUnits.frameRatio (GlobalVerticalDescentCharacter.frame (L.pullback (KernelFrame.Global.universalPoint f).left) (KernelFrame.Global.globalFrame f L Dh Kh).symm c)
    ((Vertical.ParameterKernelFrames.frames (Kernel.Scheme.kernelInclusion f) g L Dv Kv).frame l c _) = _
  rw [GlobalFrameProducts.frame_eq f L Dh Kh c k (lift_fst _ _) hk,
    Vertical.ParameterKernelFrames.frames_frame (Kernel.Scheme.kernelInclusion f) g L Dv Kv l c (lift_snd _ _).symm hl]
  exact (FrameRatioPullback.frameRatio_postcomp
    (Kh.frame k (c ≫ KernelFrame.Global.universalPoint f) hk) (Kv.frame l (c ≫ KernelFrame.Global.universalPoint f) hl)
    (Pulled.LineBilinear.fiberComparison (KernelFrame.Global.universalPoint f) L c (c ≫ KernelFrame.Global.universalPoint f) rfl).symm).trans
    (value_at f g L Dh Dv Kh Kv k l (c ≫ KernelFrame.Global.universalPoint f) hk hl).symm

variable [IsCommMonObj X] (ht : FramesTransverseTransport.Transverse f Kh Dv)

include ht

/-- Native descent of the globally trivialized first-kernel family has exactly the inverse original pairing character. -/
theorem scalar_translation {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (l : T ⟶ Kernel.Scheme.kernelObject g)
    (z w : T ⟶ X) (h : (l ≫ Kernel.Scheme.kernelInclusion g) * z = w) (q : T ⟶ Kernel.Scheme.kernelObject f ⊗ Y)
    (hz : lift k z ≫ (𝟙 (Kernel.Scheme.kernelObject f) ⊗ₘ g) = q)
    (hw : lift k w ≫ (𝟙 (Kernel.Scheme.kernelObject f) ⊗ₘ g) = q) :
    Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar (Vertical.ParameterKernelFrames.nativeDatum (Kernel.Scheme.kernelInclusion f) g L Dv Kv)
      (KernelFrame.Global.globalFrame f L Dh Kh).symm q.left (lift k z).left (lift k w).left
      (congrArg Over.Hom.left hz) (congrArg Over.Hom.left hw) =
    (ConcreteKernelPairing.Concrete.value f g L Dh Dv Kh Kv k l)⁻¹.val := by
  have hs := GlobalVerticalDescentCharacter.scalar_translation g (L.pullback (KernelFrame.Global.universalPoint f).left)
    (Vertical.ParameterKernelFrames.multiplication (Kernel.Scheme.kernelInclusion f) L Dv)
    (Vertical.ParameterKernelFrames.frames (Kernel.Scheme.kernelInclusion f) g L Dv Kv) (KernelFrame.Global.globalFrame f L Dh Kh).symm
    l z w k h q hz hw
    (GlobalFrameProducts.product f L Dh Kh Dv ht
      (lift k (l ≫ Kernel.Scheme.kernelInclusion g)) (lift k z) (lift k w)
      (CoordinateTransverseTranslations.verticalRel _ _ _ _ h) ⊤)
  exact hs.trans (congrArg (fun u : Γ(T.left, ⊤)ˣ => (u⁻¹).val) (frame_ratio f g L Dh Dv Kh Kv k l))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.GlobalDescentCharacter
