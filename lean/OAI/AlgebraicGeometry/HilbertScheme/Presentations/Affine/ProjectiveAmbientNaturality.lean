import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ProjectiveAmbient
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.PointNaturality
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.AmbientProjections

/-! # Projective Ambient Naturality -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ProjectiveAmbientNaturality.GradedHilbert

noncomputable section

/-! The affine polynomial description of the native projective ambient
commutes with arbitrary homomorphisms of test rings. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (n : ℕ) {R A : Type u} [CommRing R] [CommRing A]
variable (a : Spec (CommRingCat.of R) ⟶ S) (φ : R →+* A)

def affineTestMap : Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ a) ⟶ Over.mk a :=
  Over.homMk (Spec.map (CommRingCat.ofHom φ)) rfl

theorem affineProjectiveAmbientIso_naturality :
    (ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n (Spec.map (CommRingCat.ofHom φ) ≫ a)).hom ≫
        Hilbert.Functor.ambientMap (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (affineTestMap a φ) =
      Polynomial.ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap (n := n) φ ≫ (ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n a).hom := by
  let : Algebra R A := φ.toAlgebra
  apply (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd (Over.mk a) (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n))).hom_ext
  · change (_ ≫ _) ≫ Hilbert.Functor.ambientProjection (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a) =
      (_ ≫ _) ≫ Hilbert.Functor.ambientProjection (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a)
    rw [Category.assoc, Hilbert.AmbientProjections.ambientMap_projection, Category.assoc, ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso_projection,
      ← Category.assoc, ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso_projection]
    exact Polynomial.ProjectiveBaseChange.GradedHilbert.polynomialProjectiveCoefficientMap_over.symm
  · change (_ ≫ _) ≫ (prod.snd : Over.mk a ⨯ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n ⟶ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n).left =
      (_ ≫ _) ≫ (prod.snd : Over.mk a ⨯ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n ⟶ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n).left
    rw [Category.assoc, Hilbert.AmbientProjections.ambientMap_second, ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso_projective,
      Category.assoc, ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso_projective]
    exact Projective.PointNaturality.GradedHilbert.projectiveSchemePointMap_naturality a φ n

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ProjectiveAmbientNaturality.GradedHilbert
