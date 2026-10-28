import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.ProjectiveBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.AmbientTransport

/-! # Projective Ambient -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.ProjectiveAmbient.GradedHilbert

noncomputable section

/-! The native projective ambient over a parameter scheme is canonically
the native ambient over the original base. This identifies their actual Hilbert families. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (M : Over S) {n : ℕ} {T : Over S} (x : T ⟶ M)

theorem projectiveAmbientBaseChange_isPullback :
    IsPullback
      ((prod.snd : Over.mk x.left ⨯ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n ⟶ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n).left ≫
        Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap M.hom n)
      (Hilbert.Functor.ambientProjection (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n) (Over.mk x.left))
      (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n).hom T.hom := by
  have hlocal : IsPullback
      (prod.snd : Over.mk x.left ⨯ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n ⟶ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n).left
      (Hilbert.Functor.ambientProjection (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n) (Over.mk x.left))
      (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n).hom x.left :=
    (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd (Over.mk x.left) (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n))).flip
  have H := hlocal.paste_horiz (Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap_isPullback M.hom n)
  rwa [x.w] at H

def globalProjectiveAmbientIso :
    Hilbert.Functor.ambient (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n) (Over.mk x.left) ≅
      Hilbert.Functor.ambient (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T :=
  (projectiveAmbientBaseChange_isPullback (n := n) M x).isoIsPullback
    (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n).left T.left
    (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd T (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n))).flip

theorem globalProjectiveAmbientIso_projection :
    (globalProjectiveAmbientIso (n := n) M x).hom ≫ Hilbert.Functor.ambientProjection (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T =
      Hilbert.Functor.ambientProjection (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n) (Over.mk x.left) :=
  (projectiveAmbientBaseChange_isPullback (n := n) M x).isoIsPullback_hom_snd _ _ _

theorem globalProjectiveAmbientIso_projective :
    (globalProjectiveAmbientIso (n := n) M x).hom ≫
        (prod.snd : T ⨯ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n ⟶ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n).left =
      (prod.snd : Over.mk x.left ⨯ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n ⟶ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n).left ≫
        Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap M.hom n :=
  (projectiveAmbientBaseChange_isPullback (n := n) M x).isoIsPullback_hom_fst _ _ _

theorem globalProjectiveAmbientIso_inv_projection :
    (globalProjectiveAmbientIso (n := n) M x).inv ≫
        Hilbert.Functor.ambientProjection (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n) (Over.mk x.left) =
      Hilbert.Functor.ambientProjection (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T :=
  (projectiveAmbientBaseChange_isPullback (n := n) M x).isoIsPullback_inv_snd _ _ _

def polynomialFamilyOverOriginalBase
    (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n) (Over.mk x.left)) :
    Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T :=
  Hilbert.AmbientTransport.ambientTransport (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n)
    (globalProjectiveAmbientIso M x).symm (Iso.refl T.left)
    ((globalProjectiveAmbientIso_inv_projection M x).trans (Category.comp_id _).symm) F

theorem polynomialFamilyOverOriginalBase_val
    (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n) (Over.mk x.left)) :
    (polynomialFamilyOverOriginalBase M x F).val = F.val.comap (globalProjectiveAmbientIso M x).inv := rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.ProjectiveAmbient.GradedHilbert
