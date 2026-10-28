import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesTransverseTransport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility

/-! # Transverse Product Equivariance -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.TransverseProductEquivariance

noncomputable section

/-!
# Biextension interchange makes each product equivariant for transverse kernel translations
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesTransverseTransport

variable {S : Scheme.{u}} {A B X Y : Over S} [GrpObj A] [GrpObj X]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (hi : Biextension.Compatibility.Interchange L Dh Dv)

variable {T : Over S} (c a b x a' b' y z w : T ⟶ A ⊗ X)
  (hax : FiberwiseMultiplication.ProductRel (fst A X) (snd A X) a x y)
  (hbx : FiberwiseMultiplication.ProductRel (snd A X) (fst A X) b x z)
  (hcb : FiberwiseMultiplication.ProductRel (fst A X) (snd A X) c b b')
  (hca : FiberwiseMultiplication.ProductRel (snd A X) (fst A X) c a a')
  (hby : FiberwiseMultiplication.ProductRel (snd A X) (fst A X) b' y w)
  (haz : FiberwiseMultiplication.ProductRel (fst A X) (snd A X) a' z w)

section VerticalTranslations

variable [GrpObj Y] (g : X ⟶ Y) [IsMonHom g] (Fv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)
  (ht : Kernel.FramesTransverseTransport.Transverse g Fv Dh) (l : T ⟶ Kernel.Scheme.kernelObject g)
  (hc : l ≫ Kernel.Scheme.kernelInclusion g = c ≫ snd A X) (hb : l ≫ Kernel.Scheme.kernelInclusion g = b ≫ snd A X)
  (hb' : l ≫ Kernel.Scheme.kernelInclusion g = b' ≫ snd A X)

include hi ht hcb in
/-- The horizontal product commutes with the same transverse kernel translation on both input fibers. -/
theorem horizontal_product (U : T.left.Opens) (m : Γ(Line.Fibers.fiber L a, U)) (n : Γ(Line.Fibers.fiber L x, U)) :
    (Dh.product a' z w haz).app U
      ((Dv.product c a a' hca).app U ((Fv.frame l c hc).hom.app U (1 : Γ(T.left, U))) m)
      ((Dv.product b x z hbx).app U ((Fv.frame l b hb).hom.app U (1 : Γ(T.left, U))) n) =
    (Dv.product b' y w hby).app U ((Fv.frame l b' hb').hom.app U (1 : Γ(T.left, U)))
      ((Dh.product a x y hax).app U m n) := by
  have h := hi T c a b x a' b' y z w hax hbx hcb hca hby haz U
    ((Fv.frame l c hc).hom.app U (1 : Γ(T.left, U))) m
    ((Fv.frame l b hb).hom.app U (1 : Γ(T.left, U))) n
  rw [ht T l c b b' hc hb hb' hcb] at h
  exact h.symm

end VerticalTranslations

variable [GrpObj B] (f : A ⟶ B) [IsMonHom f] (Fh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh)
  (ht : Kernel.FramesTransverseTransport.Transverse f Fh Dv) (k : T ⟶ Kernel.Scheme.kernelObject f)
  (hc : k ≫ Kernel.Scheme.kernelInclusion f = c ≫ fst A X) (ha : k ≫ Kernel.Scheme.kernelInclusion f = a ≫ fst A X)
  (ha' : k ≫ Kernel.Scheme.kernelInclusion f = a' ≫ fst A X)

include hi ht hca in
/-- The vertical product commutes with the same horizontal kernel translation on both input fibers. -/
theorem vertical_product (U : T.left.Opens) (m : Γ(Line.Fibers.fiber L b, U)) (n : Γ(Line.Fibers.fiber L x, U)) :
    (Dv.product b' y w hby).app U
      ((Dh.product c b b' hcb).app U ((Fh.frame k c hc).hom.app U (1 : Γ(T.left, U))) m)
      ((Dh.product a x y hax).app U ((Fh.frame k a ha).hom.app U (1 : Γ(T.left, U))) n) =
    (Dh.product a' z w haz).app U ((Fh.frame k a' ha').hom.app U (1 : Γ(T.left, U)))
      ((Dv.product b x z hbx).app U m n) := by
  have h := hi T c a b x a' b' y z w hax hbx hcb hca hby haz U
    ((Fh.frame k c hc).hom.app U (1 : Γ(T.left, U)))
    ((Fh.frame k a ha).hom.app U (1 : Γ(T.left, U))) m n
  rw [ht T k c a a' hc ha ha' hca] at h
  exact h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.TransverseProductEquivariance
