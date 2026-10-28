import OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.KernelDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateKernelTransport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.TransverseCharacterRatio

/-! # Descent Translation -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.DescentTranslation

noncomputable section

/-! Native one-coordinate descent has exactly the kernel-translation scalar measured by the canonical pairing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.AxisData
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.KernelDescent OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateTransverseTranslations OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Pair
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesTransverseTransport

variable {S : Scheme.{u}} {A X Y : Over S} [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (g : X ⟶ Y) [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)

/-- The actual native gluing morphism is contraction by the included second-kernel frame. -/
theorem native_hom_translation {T : Over S} (l : T ⟶ Kernel.Scheme.kernelObject g) (z w : T ⟶ X) (x : T ⟶ A)
    (h : (l ≫ Kernel.Scheme.kernelInclusion g) * z = w) (q : T ⟶ A ⊗ Y)
    (hz : lift x z ≫ (𝟙 A ⊗ₘ g) = q) (hw : lift x w ≫ (𝟙 A ⊗ₘ g) = q) :
    (KernelDescent.nativeDatum g L Dv Kv).hom q.left (lift x z).left (lift x w).left
      (congrArg Over.Hom.left hz) (congrArg Over.Hom.left hw) =
    CoordinateTransverseTranslations.verticalTranslateTo L Dv g Kv l z w x h := by
  rw [KernelDescent.nativeDatum_hom g L Dv Kv q (lift x z) (lift x w) hz hw]
  have hd : Kernel.Pair.pointDifference g (lift x z ≫ snd A X) (lift x w ≫ snd A X)
      (KernelDescent.relation g (lift x z) (lift x w) (hz.trans hw.symm)).1 = l := by
    apply (cancel_mono (Kernel.Scheme.kernelInclusion g)).mp
    rw [Kernel.Pair.pointDifference_comp_inclusion, lift_snd, lift_snd, ← h,
      mul_comm (l ≫ Kernel.Scheme.kernelInclusion g) z, inv_mul_cancel_left]
  have ht := FiberwiseQuotientTransport.transport_using
    (snd A X) (fst A X) g Biextension.AxisData.replaceSecond Biextension.AxisData.replaceSecond_group Biextension.AxisData.replaceSecond_base L Dv Kv
    (lift x z) (lift x w) (KernelDescent.relation g (lift x z) (lift x w) (hz.trans hw.symm)) l hd
    (by rw [lift_snd, lift_snd]; exact (mul_comm _ _).trans h)
  exact ht.trans (CoordinateKernelTransport.vertical_transport g L Dv Kv l z w x h)

variable {B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L)
  (Kh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh)
  (ht : Kernel.FramesTransverseTransport.Transverse f Kh Dv)

include ht

/-- Transporting a first-kernel frame by the genuine native datum changes it by the inverse pairing value. -/
theorem native_frame_ratio {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (l : T ⟶ Kernel.Scheme.kernelObject g)
    (z w : T ⟶ X) (h : (l ≫ Kernel.Scheme.kernelInclusion g) * z = w) (q : T ⟶ A ⊗ Y)
    (hz : lift (k ≫ Kernel.Scheme.kernelInclusion f) z ≫ (𝟙 A ⊗ₘ g) = q)
    (hw : lift (k ≫ Kernel.Scheme.kernelInclusion f) w ≫ (𝟙 A ⊗ₘ g) = q) :
    Line.FrameUnits.frameRatio
      ((Kh.frame k (lift (k ≫ Kernel.Scheme.kernelInclusion f) z) (lift_fst _ _).symm) ≪≫
        (KernelDescent.nativeDatum g L Dv Kv).iso q.left (lift (k ≫ Kernel.Scheme.kernelInclusion f) z).left
          (lift (k ≫ Kernel.Scheme.kernelInclusion f) w).left (congrArg Over.Hom.left hz) (congrArg Over.Hom.left hw))
      (Kh.frame k (lift (k ≫ Kernel.Scheme.kernelInclusion f) w) (lift_fst _ _).symm) =
    (Biextension.Compatibility.kernelObstruction L Dh Dv f g Kh Kv k l
      (lift (k ≫ Kernel.Scheme.kernelInclusion f) (l ≫ Kernel.Scheme.kernelInclusion g)) (lift_fst _ _).symm (lift_snd _ _).symm)⁻¹ := by
  let c := lift (k ≫ Kernel.Scheme.kernelInclusion f) (l ≫ Kernel.Scheme.kernelInclusion g)
  let a := lift (k ≫ Kernel.Scheme.kernelInclusion f) z
  let b := lift (k ≫ Kernel.Scheme.kernelInclusion f) w
  have hr : FiberwiseMultiplication.ProductRel (snd A X) (fst A X) c a b := CoordinateTransverseTranslations.verticalRel _ _ _ _ h
  have : IsIso (Bilinear.BilinearPullback.toHom (Dv.product c a b hr)) := Dv.product_isIso c a b hr
  have he : (KernelDescent.nativeDatum g L Dv Kv).iso q.left a.left b.left
      (congrArg Over.Hom.left hz) (congrArg Over.Hom.left hw) =
      asIso (Bilinear.Contraction.contractLeft (Dv.product c a b hr)
        (Kv.frame l c (lift_snd _ _).symm).hom) := by
    apply Iso.ext
    exact native_hom_translation g L Dv Kv l z w (k ≫ Kernel.Scheme.kernelInclusion f) h q hz hw
  change Line.FrameUnits.frameRatio ((Kh.frame k a (lift_fst _ _).symm) ≪≫
    (KernelDescent.nativeDatum g L Dv Kv).iso q.left a.left b.left _ _) (Kh.frame k b (lift_fst _ _).symm) = _
  rw [he]
  exact TransverseCharacterRatio.vertical_character f g L Dh Dv Kh Kv ht k l c a b
    (lift_fst _ _).symm (lift_fst _ _).symm (lift_fst _ _).symm (lift_snd _ _).symm hr

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.DescentTranslation
