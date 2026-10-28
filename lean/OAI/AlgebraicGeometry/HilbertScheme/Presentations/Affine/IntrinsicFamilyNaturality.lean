import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.IntrinsicPolynomialFamily
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ProjectiveAmbientNaturality

/-! # Intrinsic Family Naturality -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.IntrinsicFamilyNaturality.GradedHilbert

noncomputable section

/-! The actual equivalence between native affine families and polynomial
Proj families commutes with every coefficient homomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (n : ℕ) {R A : Type u} [CommRing R] [CommRing A]
variable (a : Spec (CommRingCat.of R) ⟶ S) (φ : R →+* A)

def affinePolynomialCoefficientPullback
    (F : AbelianModuli.HilbertConstruction.Closed.Families.FlatClosedFamily (Over.mk (Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading R n)))) :
    AbelianModuli.HilbertConstruction.Closed.Families.FlatClosedFamily (Over.mk (Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading A n))) := by
  let : Algebra R A := φ.toAlgebra
  exact F.pullbackAlong (Polynomial.ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap φ) (Spec.map (CommRingCat.ofHom φ))
    Polynomial.ProjectiveBaseChange.GradedHilbert.polynomialProjective_isPullback

theorem affineNativeToPolynomial_baseChange
    (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a)) :
    IntrinsicPolynomialFamily.GradedHilbert.affineNativeToPolynomial n (Spec.map (CommRingCat.ofHom φ) ≫ a)
        (Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (ProjectiveAmbientNaturality.GradedHilbert.affineTestMap a φ) F) =
      affinePolynomialCoefficientPullback n φ (IntrinsicPolynomialFamily.GradedHilbert.affineNativeToPolynomial n a F) := by
  apply AbelianModuli.HilbertConstruction.Closed.Families.FlatClosedFamily.ext
  change (F.val.comap (Hilbert.Functor.ambientMap (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (ProjectiveAmbientNaturality.GradedHilbert.affineTestMap a φ))).comap
      (ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n (Spec.map (CommRingCat.ofHom φ) ≫ a)).hom =
    (F.val.comap (ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n a).hom).comap (Polynomial.ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap φ)
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    ProjectiveAmbientNaturality.GradedHilbert.affineProjectiveAmbientIso_naturality]

theorem affinePolynomialToNative_baseChange
    (F : AbelianModuli.HilbertConstruction.Closed.Families.FlatClosedFamily (Over.mk (Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading R n)))) :
    IntrinsicPolynomialFamily.GradedHilbert.affinePolynomialToNative n (Spec.map (CommRingCat.ofHom φ) ≫ a) (affinePolynomialCoefficientPullback n φ F) =
      Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (ProjectiveAmbientNaturality.GradedHilbert.affineTestMap a φ) (IntrinsicPolynomialFamily.GradedHilbert.affinePolynomialToNative n a F) := by
  apply (IntrinsicPolynomialFamily.GradedHilbert.affineNativePolynomialFamilyEquiv n (Spec.map (CommRingCat.ofHom φ) ≫ a)).injective
  change IntrinsicPolynomialFamily.GradedHilbert.affineNativeToPolynomial n _ (IntrinsicPolynomialFamily.GradedHilbert.affinePolynomialToNative n _ _) =
    IntrinsicPolynomialFamily.GradedHilbert.affineNativeToPolynomial n _ (Hilbert.Functor.pullbackFamily _ _ _)
  rw [affineNativeToPolynomial_baseChange]
  exact ((IntrinsicPolynomialFamily.GradedHilbert.affineNativePolynomialFamilyEquiv n _).apply_symm_apply _).trans
    (congrArg (affinePolynomialCoefficientPullback n φ) ((IntrinsicPolynomialFamily.GradedHilbert.affineNativePolynomialFamilyEquiv n a).apply_symm_apply F)).symm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.IntrinsicFamilyNaturality.GradedHilbert
