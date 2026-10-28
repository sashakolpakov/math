import OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.PullbackKernelFrames

/-! # Kernel Unit Values -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelUnitValues

noncomputable section

/-! Exact values of the target unit frames on the represented coordinate kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrameIsotropy

/-- Equality of quotient maps preserves frame values at points with the same actual inclusion. -/
theorem congr_quotient_frame {S : Scheme.{u}} {A : Over S} [GrpObj A]
    (f g : A ⟶ A) [IsMonHom f] [IsMonHom g] (h : f = g)
    (L : Line.Bundles.LineBundle (A ⊗ A).left)
    (D : FiberwiseMultiplication.Multiplication (snd A A) (fst A A) L) (K : FiberwiseMultiplication.KernelFrames (snd A A) (fst A A) L f D)
    {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (l : T ⟶ Kernel.Scheme.kernelObject g) (a : T ⟶ A ⊗ A)
    (hk : k ≫ Kernel.Scheme.kernelInclusion f = a ≫ snd A A) (hl : l ≫ Kernel.Scheme.kernelInclusion g = a ≫ snd A A) :
    (Scalar.PullbackKernelFrames.congr_quotient f g h L D K).frame l a hl = K.frame k a hk := by
  cases h
  have he : k = l := (cancel_mono (Kernel.Scheme.kernelInclusion f)).mp (hk.trans hl.symm)
  subst l
  rfl

variable {S : Scheme.{u}} {A B X Y : Over S}
  [GrpObj A] [GrpObj B] [GrpObj X] [GrpObj Y]
  (f : A ⟶ B) [IsMonHom f] (g : X ⟶ Y) [IsMonHom g]
  (L : Line.Bundles.LineBundle (B ⊗ Y).left)
  (Dv : FiberwiseMultiplication.Multiplication (snd B Y) (fst B Y) L)

omit [GrpObj A] [GrpObj B] [IsMonHom f] in
/-- The inverse-image identity-kernel frame is exactly the transported target unit frame. -/
theorem vertical_frame {T : Over S} (l : T ⟶ Kernel.Scheme.kernelObject (g ≫ 𝟙 Y)) (a : T ⟶ A ⊗ X)
    (hl : l ≫ Kernel.Scheme.kernelInclusion (g ≫ 𝟙 Y) = a ≫ snd A X)
    (hz : (a ≫ (f ⊗ₘ g)) ≫ snd B Y = 1) :
    (KernelFrameIsotropy.vertical f g L Dv).frame l a hl =
      LineSection.transportFrame (f ⊗ₘ g) L a (a ≫ (f ⊗ₘ g)) rfl
        (Dv.unitFrame (a ≫ (f ⊗ₘ g)) hz) := by
  have hm : (l ≫ Kernel.PreimageQuotient.map g (𝟙 Y)) ≫ Kernel.Scheme.kernelInclusion (𝟙 Y) =
      (a ≫ (f ⊗ₘ g)) ≫ snd B Y := by
    rw [Category.assoc, Kernel.PreimageQuotient.map_inclusion, ← Category.assoc, hl]
    simp
  unfold KernelFrameIsotropy.vertical
  rw [KernelFrame.SquareValues.frames_frame _ _ _ _ _ _ _ _ _ _ _ _ _ l a hl hm]
  rfl

omit [GrpObj A] [GrpObj B] [IsMonHom f] in
/-- The same actual frame may be expressed at a specified neutral target point. -/
theorem vertical_frame_to {T : Over S} (l : T ⟶ Kernel.Scheme.kernelObject (g ≫ 𝟙 Y)) (a : T ⟶ A ⊗ X)
    (hl : l ≫ Kernel.Scheme.kernelInclusion (g ≫ 𝟙 Y) = a ≫ snd A X)
    (b : T ⟶ B ⊗ Y) (hb : a ≫ (f ⊗ₘ g) = b) (hz : b ≫ snd B Y = 1) :
    (KernelFrameIsotropy.vertical f g L Dv).frame l a hl =
      LineSection.transportFrame (f ⊗ₘ g) L a b hb (Dv.unitFrame b hz) := by
  subst b
  exact vertical_frame f g L Dv l a hl hz

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelUnitValues
