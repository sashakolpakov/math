import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Point
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Functor

/-! # Projective Ambient -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ProjectiveAmbient.GradedHilbert

noncomputable section

/-! On an affine spectrum test, the native relative projective ambient is
canonically the polynomial projective space over its coefficient ring. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (n : ℕ) {R : Type u} [CommRing R]
variable (a : Spec (CommRingCat.of R) ⟶ S)

def affineProjectiveAmbientIso : Proj (Hilbert.Polynomial.GradedHilbert.grading R n) ≅
    Hilbert.Functor.ambient (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a) :=
  (Projective.Point.GradedHilbert.projectiveSchemePointMap_isPullback n a).isoIsPullback (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n).left (Spec (CommRingCat.of R))
    (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd (Over.mk a) (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n))).flip

theorem affineProjectiveAmbientIso_projection :
    (affineProjectiveAmbientIso n a).hom ≫ Hilbert.Functor.ambientProjection (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a) =
      Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading R n) :=
  (Projective.Point.GradedHilbert.projectiveSchemePointMap_isPullback n a).isoIsPullback_hom_snd _ _ _

theorem affineProjectiveAmbientIso_projective :
    (affineProjectiveAmbientIso n a).hom ≫
        (prod.snd : Over.mk a ⨯ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n ⟶ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n).left =
      Projective.Point.GradedHilbert.projectiveSchemePointMap n a :=
  (Projective.Point.GradedHilbert.projectiveSchemePointMap_isPullback n a).isoIsPullback_hom_fst _ _ _

theorem affineProjectiveAmbientIso_inv_projection :
    (affineProjectiveAmbientIso n a).inv ≫ Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading R n) =
      Hilbert.Functor.ambientProjection (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a) :=
  (Projective.Point.GradedHilbert.projectiveSchemePointMap_isPullback n a).isoIsPullback_inv_snd _ _ _

theorem affineProjectiveAmbientIso_isPullback :
    IsPullback (affineProjectiveAmbientIso n a).hom (Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading R n))
      (Hilbert.Functor.ambientProjection (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a)) (𝟙 (Spec (CommRingCat.of R))) :=
  IsPullback.of_horiz_isIso ⟨(affineProjectiveAmbientIso_projection n a).trans (Category.comp_id _).symm⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ProjectiveAmbient.GradedHilbert
