import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.HomogeneousCoordinateBaseChange

/-! # Coefficient Composition -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.CoefficientComposition.GradedHilbert

noncomputable section

/-! Saturating canonical homogeneous coordinates between coefficient
extensions does not alter the resulting projective family or final saturation. -/

universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] {n : ℕ}

theorem projectiveSaturation_map_saturation (φ : R →+* A) (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    Projective.Saturation.GradedHilbert.projectiveSaturation ((Projective.Saturation.GradedHilbert.projectiveSaturation I).map (Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ)) =
      Projective.Saturation.GradedHilbert.projectiveSaturation (I.map (Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ)) := by
  apply congrArg ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf
  rw [Affine.HomogeneousCoordinateBaseChange.GradedHilbert.projectiveQuotientInclusion_coefficient_ker, Affine.HomogeneousCoordinateBaseChange.GradedHilbert.projectiveQuotientInclusion_coefficient_ker,
    Projective.Saturation.GradedHilbert.projectiveSaturation_idealSheaf]

theorem homogeneousIdeal_coefficient_map_comp (φ : R →+* A) (ψ : A →+* B)
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    (I.map (Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ)).map (Graded.BaseChange.GradedHilbert.gradedCoefficientMap ψ) =
      I.map (Graded.BaseChange.GradedHilbert.gradedCoefficientMap (ψ.comp φ)) := by
  apply HomogeneousIdeal.ext
  change Ideal.map (MvPolynomial.map ψ) (Ideal.map (MvPolynomial.map φ) I.toIdeal) =
    Ideal.map (MvPolynomial.map (ψ.comp φ)) I.toIdeal
  rw [Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro f
  exact MvPolynomial.map_map φ ψ f

theorem projectiveSaturation_coefficient_comp (φ : R →+* A) (ψ : A →+* B)
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    Projective.Saturation.GradedHilbert.projectiveSaturation ((Projective.Saturation.GradedHilbert.projectiveSaturation (I.map (Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ))).map (Graded.BaseChange.GradedHilbert.gradedCoefficientMap ψ)) =
      Projective.Saturation.GradedHilbert.projectiveSaturation (I.map (Graded.BaseChange.GradedHilbert.gradedCoefficientMap (ψ.comp φ))) := by
  rw [projectiveSaturation_map_saturation, homogeneousIdeal_coefficient_map_comp]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.CoefficientComposition.GradedHilbert
