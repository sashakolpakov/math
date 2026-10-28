import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.HomogeneousChartEquations
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.ChartIdeals
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates

/-! # Projective Family Equations -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.ProjectiveFamilyEquations.GradedHilbert

noncomputable section

/-! Actual finitely presented projective families admit finite homogeneous
equations over arbitrary coefficient rings, with equality of their defining ideal sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {R : Type u} [CommRing R] {n : ℕ}

theorem finite_homogeneous_projective_equations (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    [LocallyOfFinitePresentation (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))] :
    ∃ J : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n), J.toIdeal.FG ∧ J ≤ I ∧
      Projective.Saturation.GradedHilbert.projectiveSaturation J = Projective.Saturation.GradedHilbert.projectiveSaturation I := by
  obtain ⟨J, hfg, hle, hchart⟩ := HomogeneousChartEquations.GradedHilbert.finite_homogeneous_same_chart_ideals I
    (Projective.ChartEquationFiniteness.GradedHilbert.projectiveQuotient_dehomogenizedIdeal_fg I)
  exact ⟨J, hfg, hle, Saturation.ChartIdeals.GradedHilbert.projectiveSaturation_eq_of_dehomogenized J I hchart⟩

theorem finite_homogeneous_saturated_equations (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (hI : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal)
    [LocallyOfFinitePresentation (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))] :
    ∃ J : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n), J.toIdeal.FG ∧ J ≤ I ∧ Projective.Saturation.GradedHilbert.projectiveSaturation J = I := by
  obtain ⟨J, hfg, hle, hs⟩ := finite_homogeneous_projective_equations I
  exact ⟨J, hfg, hle, hs.trans (Projective.Saturation.GradedHilbert.projectiveSaturation_eq_of_saturated I hI)⟩

theorem native_affine_finite_homogeneous_equations {S : Scheme.{u}}
    (a : Spec (CommRingCat.of R) ⟶ S)
    (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a)) :
    ∃ J : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n), J.toIdeal.FG ∧
      (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion J ≫ (Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n a).hom).ker = F.val := by
  let I := Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n a F
  have : LocallyOfFinitePresentation (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)) :=
    Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_locallyOfFinitePresentation n a F
  obtain ⟨J, hfg, _, hs⟩ := finite_homogeneous_saturated_equations I
    (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_saturated n a F)
  refine ⟨J, hfg, ?_⟩
  rw [Global.PolynomialInclusion.closedImmersion_comp_iso_ker, ← Projective.Saturation.GradedHilbert.projectiveSaturation_idealSheaf J, hs]
  exact (Global.PolynomialInclusion.closedImmersion_comp_iso_ker (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I)
    (Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n a)).symm.trans (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_global_kernel n a F)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.ProjectiveFamilyEquations.GradedHilbert
