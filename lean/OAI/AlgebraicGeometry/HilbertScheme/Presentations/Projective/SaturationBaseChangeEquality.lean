import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.HomogeneousCoordinateBaseChange

/-! # Saturation Base Change Equality -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.SaturationBaseChangeEquality.GradedHilbert

noncomputable section

/-! Equality of projective saturated ideals remains equality after
arbitrary coefficient extension and projective saturation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {R A : Type u} [CommRing R] [CommRing A] {n : ℕ}

theorem projectiveSaturation_map_eq_of_eq (φ : R →+* A)
    (I J : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (h : Saturation.GradedHilbert.projectiveSaturation I = Saturation.GradedHilbert.projectiveSaturation J) :
    Saturation.GradedHilbert.projectiveSaturation (I.map (Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ)) =
      Saturation.GradedHilbert.projectiveSaturation (J.map (Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ)) := by
  have hk : (Quotient.GradedHilbert.projectiveQuotientInclusion I).ker = (Quotient.GradedHilbert.projectiveQuotientInclusion J).ker :=
    (Saturation.GradedHilbert.projectiveSaturation_idealSheaf I).symm.trans
      ((congrArg (fun K => (Quotient.GradedHilbert.projectiveQuotientInclusion K).ker) h).trans
        (Saturation.GradedHilbert.projectiveSaturation_idealSheaf J))
  have he : (Quotient.GradedHilbert.projectiveQuotientInclusion (I.map (Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ))).ker =
      (Quotient.GradedHilbert.projectiveQuotientInclusion (J.map (Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ))).ker :=
    (Affine.HomogeneousCoordinateBaseChange.GradedHilbert.projectiveQuotientInclusion_coefficient_ker φ I).trans
      ((congrArg (fun K => K.comap (Polynomial.ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap φ)) hk).trans
        (Affine.HomogeneousCoordinateBaseChange.GradedHilbert.projectiveQuotientInclusion_coefficient_ker φ J).symm)
  exact congrArg ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf he

theorem projectiveSaturation_extended_eq_of_eq [Algebra R A]
    (I J : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (h : Saturation.GradedHilbert.projectiveSaturation I = Saturation.GradedHilbert.projectiveSaturation J) :
    Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I) =
      Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) J) :=
  projectiveSaturation_map_eq_of_eq (algebraMap R A) I J h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.SaturationBaseChangeEquality.GradedHilbert
