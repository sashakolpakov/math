import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ProductFrames
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesTransverseTransport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility

/-! # Transverse Character Ratio -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.TransverseCharacterRatio

noncomputable section

/-! The character of a kernel translation on a transverse frame is the inverse of its actual pairing obstruction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ProductFrames
open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesTransverseTransport

/-- Reversing the two actual frames inverts their unit-valued ratio. -/
theorem frameRatio_reverse {X : Scheme.{u}} {M : X.Modules} (s t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ M) :
    Line.FrameUnits.frameRatio t s = (Line.FrameUnits.frameRatio s t)⁻¹ := by
  apply Units.ext
  rfl

/-- Contraction by a different input frame changes the output frame by exactly the input frame ratio. -/
theorem contraction_ratio {X : Scheme.{u}} {M N P : X.Modules}
    (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) [IsIso (Bilinear.BilinearPullback.toHom β)]
    (s t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ M) (a : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ N) (b : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ P)
    (hb : β.app ⊤ (t.hom.app ⊤ (1 : Γ(X, ⊤))) (a.hom.app ⊤ (1 : Γ(X, ⊤))) =
      b.hom.app ⊤ (1 : Γ(X, ⊤))) :
    Line.FrameUnits.frameRatio (a ≪≫ asIso (Bilinear.Contraction.contractLeft β s.hom)) b = Line.FrameUnits.frameRatio s t := by
  have h := FrameRatioMultiplication.frameRatio_product β s t a a (Bilinear.ProductFrames.productFrame β s a) b
    (Bilinear.ProductFrames.productFrame_app β s a ⊤).symm hb
  rw [(Line.FrameUnits.frameRatio_eq_one_iff a a).mpr rfl, mul_one] at h
  exact h

variable {S : Scheme.{u}} {A B X Y : Over S} [GrpObj A] [GrpObj B] [GrpObj X] [GrpObj Y]
  (f : A ⟶ B) [IsMonHom f] (g : X ⟶ Y) [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh) (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)
  (ht : Kernel.FramesTransverseTransport.Transverse f Kh Dv)

include ht

/-- The scalar by which the actual second-kernel translation changes the first-kernel frame is the inverse pairing. -/
theorem vertical_character {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (l : T ⟶ Kernel.Scheme.kernelObject g)
    (c a b : T ⟶ A ⊗ X) (hc : k ≫ Kernel.Scheme.kernelInclusion f = c ≫ fst A X)
    (ha : k ≫ Kernel.Scheme.kernelInclusion f = a ≫ fst A X) (hb : k ≫ Kernel.Scheme.kernelInclusion f = b ≫ fst A X)
    (hl : l ≫ Kernel.Scheme.kernelInclusion g = c ≫ snd A X) (h : FiberwiseMultiplication.ProductRel (snd A X) (fst A X) c a b) :
    letI := Dv.product_isIso c a b h
    Line.FrameUnits.frameRatio ((Kh.frame k a ha) ≪≫ asIso (Bilinear.Contraction.contractLeft (Dv.product c a b h) (Kv.frame l c hl).hom))
      (Kh.frame k b hb) =
      (Biextension.Compatibility.kernelObstruction L Dh Dv f g Kh Kv k l c hc hl)⁻¹ := by
  have : IsIso (Bilinear.BilinearPullback.toHom (Dv.product c a b h)) := Dv.product_isIso c a b h
  exact (contraction_ratio (Dv.product c a b h) (Kv.frame l c hl) (Kh.frame k c hc)
    (Kh.frame k a ha) (Kh.frame k b hb) (ht T k c a b hc ha hb h ⊤)).trans
    (frameRatio_reverse (Kh.frame k c hc) (Kv.frame l c hl))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.TransverseCharacterRatio
