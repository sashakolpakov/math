import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.PowerFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.RestrictionCoordinates
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.PolynomialScalars

/-! # Power Frame Restrictions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PowerFrameRestrictions

noncomputable section

/-! Positive-degree frames on projective quotient charts commute with restriction whenever the same coordinate remains inverted. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.PolynomialScalars.ProjectiveCech

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem coordinateChartPowerSectionEquiv_restriction
    {s t : Finset (Fin (n + 1))} (h : s ⊆ t) (i : Fin (n + 1)) (hi : i ∈ s) (k : ℕ)
    (x : Coefficient.AlgebraPresheaf.coefficientAlgebraSections (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
      (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s)) :
    (ProjectiveChart.PowerFrames.coordinateChartPowerSectionEquiv I t i (h hi) k
      ((Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).presheaf.map (homOfLE (ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I h)).op x)).val =
      HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) h
        (ProjectiveChart.PowerFrames.coordinateChartPowerSectionEquiv I s i hi k x).val := by
  change (X i : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) ^ k •
      (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartSectionEquiv I t ⟨i, h hi⟩
        ((Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).presheaf.map (homOfLE (ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I h)).op x)).val =
    HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) h
      ((X i : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) ^ k • (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartSectionEquiv I s ⟨i, hi⟩ x).val)
  exact (congrArg (fun z : HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.ModuleChart R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) t =>
    (X i : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) ^ k • z)
      (ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartSectionEquiv_restriction I ⟨i, hi⟩ ⟨i, h hi⟩ h x)).trans
    (HilbertScheme.Presentations.Cech.PolynomialScalars.ProjectiveCech.moduleChartRestriction_polynomial_smul R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) h (X i ^ k) _).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PowerFrameRestrictions
