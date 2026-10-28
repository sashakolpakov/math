import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.IntrinsicFamilyNaturality
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.Polynomial

/-! # Homogeneous Coordinate Base Change -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.HomogeneousCoordinateBaseChange.GradedHilbert

noncomputable section

/-! Canonical homogeneous coordinates of arbitrary native affine families
commute with coefficient extension followed by projective saturation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {R A : Type u} [CommRing R] [CommRing A] {n : ℕ} (φ : R →+* A)

theorem projectiveQuotientInclusion_coefficient_ker (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (I.map (Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ))).ker =
      (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I).ker.comap (Polynomial.ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap φ) := by
  let : Algebra R A := φ.toAlgebra
  let h := Polynomial.ProjectiveBaseChange.GradedHilbert.projectiveQuotientCoefficientInclusion_isPullback (S := A) I
  change (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I)).ker = _
  rw [← h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  rfl

variable {S : Scheme.{u}} (n : ℕ) (a : Spec (CommRingCat.of R) ⟶ S)

theorem affineNativeHomogeneousIdeal_baseChange
    (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a)) :
    IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n (Spec.map (CommRingCat.ofHom φ) ≫ a)
        (Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (ProjectiveAmbientNaturality.GradedHilbert.affineTestMap a φ) F) =
      Projective.Saturation.GradedHilbert.projectiveSaturation ((IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n a F).map (Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ)) := by
  let I := IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n a F
  have hi : (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I).ker = (IntrinsicPolynomialFamily.GradedHilbert.affineNativeToPolynomial n a F).ideal :=
    Projective.IdealEquivalence.GradedHilbert.projectiveQuotient_homogeneousIdealOfSheaf _
  have he : (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (I.map (Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ))).ker =
      (IntrinsicPolynomialFamily.GradedHilbert.affineNativeToPolynomial n a F).ideal.comap (Polynomial.ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap φ) :=
    (projectiveQuotientInclusion_coefficient_ker φ I).trans
      (congrArg (fun J => J.comap (Polynomial.ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap φ)) hi)
  dsimp only [IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal]
  rw [IntrinsicFamilyNaturality.GradedHilbert.affineNativeToPolynomial_baseChange]
  exact congrArg ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf he.symm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.HomogeneousCoordinateBaseChange.GradedHilbert
