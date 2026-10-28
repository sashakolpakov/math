import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Localized.DegreePowerFrames
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.EventualDegreeFlatness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.SectionCoordinates

/-! # Power Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.PowerFrames

noncomputable section

/-! Actual functions on a projective coordinate chart give explicit frames for each positive homogeneous degree after localization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial DirectSum
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.EventualDegreeFlatness.ProjectiveCech

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def coordinateChartPowerFrame (s : Finset (Fin (n + 1))) (i : Fin (n + 1)) (hi : i ∈ s) (k : ℕ) :
    HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) s 0 ≃ₗ[R]
      HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) s (k : ℤ) :=
  Localized.DegreePowerFrames.localizedDegreePowerEquiv (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.polynomialIntegerGrading R) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I)
    (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s) (s.card : ℤ) (HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.inversionMonomial_integer_degree R s)
    (X i) (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R (s.erase i)) (HilbertScheme.Presentations.EventualDegreeFlatness.ProjectiveCech.inversionMonomial_factor_variable R s i hi)
    (isWeightedHomogeneous_X R (fun _ : Fin (n + 1) => (1 : ℤ)) i) k

theorem coordinateChartPowerFrame_val (s : Finset (Fin (n + 1))) (i : Fin (n + 1)) (hi : i ∈ s) (k : ℕ)
    (x : HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) s 0) :
    (coordinateChartPowerFrame I s i hi k x).val = (X i : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) ^ k • x.val := rfl

def coordinateChartPowerSectionEquiv (s : Finset (Fin (n + 1))) (i : Fin (n + 1)) (hi : i ∈ s) (k : ℕ) :
    Coefficient.AlgebraPresheaf.coefficientAlgebraSections (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
      (SectionCoordinates.coordinateProjectiveChartOpen I s) ≃ₗ[R]
        HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) s (k : ℤ) :=
  (SectionCoordinates.coordinateProjectiveChartSectionEquiv I s ⟨i, hi⟩).trans (coordinateChartPowerFrame I s i hi k)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.PowerFrames
