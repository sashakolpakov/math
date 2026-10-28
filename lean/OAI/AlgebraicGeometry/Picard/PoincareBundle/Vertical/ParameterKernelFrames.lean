import OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.SquareValues
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.KernelDescent

/-! # Parameter Kernel Frames -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ParameterKernelFrames

noncomputable section

/-! Changing the parameter scheme preserves the actual vertical multiplication and its full kernel-frame system. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplicationPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

variable {S : Scheme.{u}} {K A X Y : Over S} [GrpObj X] [GrpObj Y]
  (t : K ⟶ A) (g : X ⟶ Y) [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)

/-- The parameter pullback first retains its original image coordinate. -/
def imageMultiplication : FiberwiseMultiplication.Multiplication (snd K X) (fst K X ≫ t) (L.pullback (t ⊗ₘ 𝟙 X).left) :=
  MultiplicationCoordinates.congrCoordinates
    (FiberwiseMultiplicationPullback.pullbackMultiplication (snd A X) (fst A X) (t ⊗ₘ 𝟙 X) L Dv) (by simp) (by simp)

/-- Refining the fixed coordinate gives the complete multiplication on the parameter family. -/
def multiplication : FiberwiseMultiplication.Multiplication (snd K X) (fst K X) (L.pullback (t ⊗ₘ 𝟙 X).left) :=
  MultiplicationFixedMap.restrictFixed (snd K X) (fst K X) t (L.pullback (t ⊗ₘ 𝟙 X).left)
    (imageMultiplication t L Dv)

/-- Every original kernel frame pulls back to the actual parameter family. -/
def imageFrames : FiberwiseMultiplication.KernelFrames (snd K X) (fst K X ≫ t) (L.pullback (t ⊗ₘ 𝟙 X).left) g
    (imageMultiplication t L Dv) :=
  Kernel.FramesPullback.congrCoordinates g (L.pullback (t ⊗ₘ 𝟙 X).left)
    (FiberwiseMultiplicationPullback.pullbackMultiplication (snd A X) (fst A X) (t ⊗ₘ 𝟙 X) L Dv)
    (Kernel.FramesPullback.pullbackFrames (snd A X) (fst A X) (t ⊗ₘ 𝟙 X) g L Dv Kv) (by simp) (by simp)

/-- The full kernel-frame system on the new parameter scheme uses the same actual kernel group scheme. -/
def frames : FiberwiseMultiplication.KernelFrames (snd K X) (fst K X) (L.pullback (t ⊗ₘ 𝟙 X).left) g (multiplication t L Dv) :=
  KernelFrame.FixedMap.restrictFixed (snd K X) (fst K X) t g (L.pullback (t ⊗ₘ 𝟙 X).left)
    (imageMultiplication t L Dv) (imageFrames t g L Dv Kv)

/-- The constructed parameter frame is exactly the original frame through the canonical fiber comparison. -/
theorem frames_frame {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject g) (a : T ⟶ K ⊗ X)
    (ha : k ≫ Kernel.Scheme.kernelInclusion g = a ≫ snd K X)
    (hb : k ≫ Kernel.Scheme.kernelInclusion g = (a ≫ (t ⊗ₘ 𝟙 X)) ≫ snd A X) :
    (frames t g L Dv Kv).frame k a ha =
      Pulled.LineSection.transportFrame (t ⊗ₘ 𝟙 X) L a (a ≫ (t ⊗ₘ 𝟙 X)) rfl (Kv.frame k _ hb) := by
  unfold frames KernelFrame.FixedMap.restrictFixed
  dsimp only
  unfold imageFrames
  rw [KernelFrame.SquareValues.congrCoordinates_frame g (L.pullback (t ⊗ₘ 𝟙 X).left)
    (FiberwiseMultiplicationPullback.pullbackMultiplication (snd A X) (fst A X) (t ⊗ₘ 𝟙 X) L Dv)
    (Kernel.FramesPullback.pullbackFrames (snd A X) (fst A X) (t ⊗ₘ 𝟙 X) g L Dv Kv)
    (by simp) (by simp) k a ha (by simpa only [Category.assoc] using hb)]
  rfl

variable [IsCommMonObj X]

/-- The parameter family carries ordinary native descent through the same full quotient kernel. -/
def nativeDatum : Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent (𝟙 K ⊗ₘ g).left :=
  KernelDescent.nativeDatum g (L.pullback (t ⊗ₘ 𝟙 X).left)
    (multiplication t L Dv) (frames t g L Dv Kv)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ParameterKernelFrames
