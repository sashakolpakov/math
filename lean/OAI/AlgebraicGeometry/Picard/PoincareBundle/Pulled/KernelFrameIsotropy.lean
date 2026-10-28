import OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.SquareValues
import OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.SquareTransverse
import OAI.AlgebraicGeometry.Picard.PoincareBundle.IdentityKernelFrames
import OAI.AlgebraicGeometry.Picard.PoincareBundle.SecondTransverseFrameUnits

/-! # Kernel Frame Isotropy -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrameIsotropy

noncomputable section

/-! The inverse-image kernel is orthogonal to the coordinate quotient kernel in the pulled line family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationPullbackSquare

variable {S : Scheme.{u}} {A B C X Y : Over S}
  [GrpObj A] [GrpObj B] [GrpObj C] [GrpObj X] [GrpObj Y]
  (f : A ⟶ B) [IsMonHom f] (g : X ⟶ Y) [IsMonHom g]
  (L : Line.Bundles.LineBundle (B ⊗ Y).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst B Y) (snd B Y) L) (Dv : FiberwiseMultiplication.Multiplication (snd B Y) (fst B Y) L)
  (m : B ⟶ C) [IsMonHom m] (K : FiberwiseMultiplication.KernelFrames (fst B Y) (snd B Y) L m Dh)

/-- The first multiplication is pulled through both genuine coordinate homomorphisms. -/
def horizontalMultiplication := MultiplicationPullbackSquare.multiplication (fst A X) (snd A X) (fst B Y) (snd B Y)
  (f ⊗ₘ g) f g (by simp) (by simp) L Dh

/-- The second multiplication is pulled through both genuine coordinate homomorphisms. -/
def verticalMultiplication := MultiplicationPullbackSquare.multiplication (snd A X) (fst A X) (snd B Y) (fst B Y)
  (f ⊗ₘ g) g f (by simp) (by simp) L Dv

/-- The first frames use the full scheme-theoretic inverse image of the target kernel. -/
def horizontal : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) (L.pullback (f ⊗ₘ g).left) (f ≫ m)
    (horizontalMultiplication f g L Dh) :=
  KernelFrame.PullbackSquare.frames (fst A X) (snd A X) (fst B Y) (snd B Y)
    (f ⊗ₘ g) f g (by simp) (by simp) L Dh m K

/-- The second frames are the pulled target unit frames on the full coordinate kernel. -/
def vertical : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) (L.pullback (f ⊗ₘ g).left) (g ≫ 𝟙 Y)
    (verticalMultiplication f g L Dv) := by
  have : Mono (lift (snd B Y) (fst B Y)) := by
    have h : lift (snd B Y) (fst B Y) = (β_ B Y).hom := by cat_disch
    rw [h]
    infer_instance
  exact KernelFrame.PullbackSquare.frames (snd A X) (fst A X) (snd B Y) (fst B Y)
    (f ⊗ₘ g) g f (by simp) (by simp) L Dv (𝟙 Y)
    (IdentityKernelFrames.frames (snd B Y) (fst B Y) L Dv)

variable (ht : Kernel.FramesTransverseTransport.Transverse m K Dv)

include ht

/-- The actual inverse-image frames retain transverse multiplication after pullback. -/
theorem horizontal_transverse : Kernel.FramesTransverseTransport.Transverse (f ≫ m)
    (horizontal f g L Dh m K) (verticalMultiplication f g L Dv) :=
  KernelFrame.SquareTransverse.frames_transverse (fst A X) (snd A X) (fst B Y) (snd B Y)
    (f ⊗ₘ g) f g (by simp) (by simp) L Dh Dv m K ht

/-- At every actual pair of inverse-image and coordinate-kernel points, the two line frames agree. -/
theorem frames_eq {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject (f ≫ m)) (l : T ⟶ Kernel.Scheme.kernelObject (g ≫ 𝟙 Y))
    (a : T ⟶ A ⊗ X) (ha : k ≫ Kernel.Scheme.kernelInclusion (f ≫ m) = a ≫ fst A X)
    (hb : l ≫ Kernel.Scheme.kernelInclusion (g ≫ 𝟙 Y) = a ≫ snd A X) :
    (horizontal f g L Dh m K).frame k a ha = (vertical f g L Dv).frame l a hb := by
  have hk : (k ≫ Kernel.PreimageQuotient.map f m) ≫ Kernel.Scheme.kernelInclusion m =
      (a ≫ (f ⊗ₘ g)) ≫ fst B Y := by
    rw [Category.assoc, Kernel.PreimageQuotient.map_inclusion, ← Category.assoc, ha]
    simp
  have hl : (l ≫ Kernel.PreimageQuotient.map g (𝟙 Y)) ≫ Kernel.Scheme.kernelInclusion (𝟙 Y) =
      (a ≫ (f ⊗ₘ g)) ≫ snd B Y := by
    rw [Category.assoc, Kernel.PreimageQuotient.map_inclusion, ← Category.assoc, hb]
    simp
  have hz : (a ≫ (f ⊗ₘ g)) ≫ snd B Y = 1 :=
    IdentityKernelFrames.coordinate_one (snd B Y) _ _ hl
  unfold horizontal vertical
  rw [KernelFrame.SquareValues.frames_frame _ _ _ _ _ _ _ _ _ _ _ _ _ k a ha hk,
    KernelFrame.SquareValues.frames_frame _ _ _ _ _ _ _ _ _ _ _ _ _ l a hb hl]
  exact congrArg (LineSection.transportFrame (f ⊗ₘ g) L a (a ≫ (f ⊗ₘ g)) rfl)
    (SecondTransverseFrameUnits.horizontal_frame_eq_vertical_unit m L Dh Dv K ht
      (k ≫ Kernel.PreimageQuotient.map f m) (a ≫ (f ⊗ₘ g)) hk hz)

/-- The actual normalized-frame pairing is one on the full inverse-image kernel against the coordinate kernel. -/
theorem isotropic : Biextension.Compatibility.Isotropic (L.pullback (f ⊗ₘ g).left)
    (horizontalMultiplication f g L Dh) (verticalMultiplication f g L Dv) (f ≫ m) (g ≫ 𝟙 Y)
    (horizontal f g L Dh m K) (vertical f g L Dv) := by
  intro T k l a ha hb
  exact (Line.FrameUnits.frameRatio_eq_one_iff _ _).mpr (frames_eq f g L Dh Dv m K ht k l a ha hb)

omit ht in
/-- The coordinate-kernel unit frames retain the actual transverse law from target interchange. -/
theorem vertical_transverse (hi : Biextension.Compatibility.Interchange L Dh Dv) :
    Kernel.FramesTransverseTransport.Transverse (g ≫ 𝟙 Y)
      (vertical f g L Dv) (horizontalMultiplication f g L Dh) := by
  have : Mono (lift (snd B Y) (fst B Y)) := by
    have h : lift (snd B Y) (fst B Y) = (β_ B Y).hom := by cat_disch
    rw [h]
    infer_instance
  exact KernelFrame.SquareTransverse.frames_transverse (snd A X) (fst A X) (snd B Y) (fst B Y)
    (f ⊗ₘ g) g f (by simp) (by simp) L Dv Dh (𝟙 Y)
    (IdentityKernelFrames.frames (snd B Y) (fst B Y) L Dv)
    (IdentityKernelFrames.transverse (snd B Y) (fst B Y) L Dv Dh
      (fun _T a b c ha hb hc h U =>
        InterchangeNeutralFrames.vertical_units_horizontal_product L Dh Dv hi a b c ha hb hc h U))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrameIsotropy
