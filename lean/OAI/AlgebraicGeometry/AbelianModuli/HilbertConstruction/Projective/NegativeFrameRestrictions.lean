import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.NegativeChartFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.RestrictionCoordinates
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.PolynomialScalars

/-! # Negative Frame Restrictions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.NegativeFrameRestrictions

noncomputable section

/-! Negative-degree chart frames commute with restriction, proved by cancellation of the inverted coordinate power. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.PolynomialScalars.ProjectiveCech

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem coordinateChartPower_smul_injective (s : Finset (Fin (n + 1))) (i : Fin (n + 1))
    (hi : i ∈ s) (k : ℕ) :
    Function.Injective (fun x : HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.ModuleChart R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) s ↦
      (X i : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) ^ k • x) :=
  (HilbertScheme.Presentations.Localized.DegreeShift.GradedModules.localizedScalarPowerEquiv (R := R) (M := HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
    (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s) (X i) (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R (s.erase i))
    (HilbertScheme.Presentations.EventualDegreeFlatness.ProjectiveCech.inversionMonomial_factor_variable R s i hi) k).injective

theorem coordinateChartNegativePowerSectionEquiv_restriction
    {s t : Finset (Fin (n + 1))} (h : s ⊆ t) (i : Fin (n + 1)) (hi : i ∈ s) (k : ℕ)
    (x : Coefficient.AlgebraPresheaf.coefficientAlgebraSections (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
      (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s)) :
    (NegativeChartFrames.coordinateChartNegativePowerSectionEquiv I t i (h hi) k
      ((Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).presheaf.map (homOfLE (ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I h)).op x)).val =
      HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) h
        (NegativeChartFrames.coordinateChartNegativePowerSectionEquiv I s i hi k x).val := by
  apply coordinateChartPower_smul_injective I t i (h hi) k
  have hleft := NegativeChartFrames.coordinateChartNegativePowerFrame_cancel I t i (h hi) k
    (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartSectionEquiv I t ⟨i, h hi⟩
      ((Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).presheaf.map
        (homOfLE (ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I h)).op x))
  have hright := NegativeChartFrames.coordinateChartNegativePowerFrame_cancel I s i hi k
    (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartSectionEquiv I s ⟨i, hi⟩ x)
  have hres := ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartSectionEquiv_restriction I ⟨i, hi⟩ ⟨i, h hi⟩ h x
  exact hleft.trans (hres.trans ((congrArg
    (HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) h) hright.symm).trans
      (HilbertScheme.Presentations.Cech.PolynomialScalars.ProjectiveCech.moduleChartRestriction_polynomial_smul R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) h (X i ^ k) _)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.NegativeFrameRestrictions
