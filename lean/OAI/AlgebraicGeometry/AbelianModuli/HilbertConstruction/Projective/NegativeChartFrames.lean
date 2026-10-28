import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Localized.NegativePowerFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.PowerFrames

/-! # Negative Chart Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.NegativeChartFrames

noncomputable section

/-! Actual regular functions on projective coordinate charts frame negative homogeneous localization degrees. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def coordinateChartNegativePowerFrame (s : Finset (Fin (n + 1))) (i : Fin (n + 1))
    (hi : i ∈ s) (k : ℕ) :
    HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) s 0 ≃ₗ[R]
      HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) s (-(k : ℤ)) :=
  Localized.NegativePowerFrames.localizedDegreeNegativePowerEquiv (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.polynomialIntegerGrading R) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I)
    (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s) (s.card : ℤ) (HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.inversionMonomial_integer_degree R s)
    (X i) (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R (s.erase i)) (HilbertScheme.Presentations.EventualDegreeFlatness.ProjectiveCech.inversionMonomial_factor_variable R s i hi)
    (isWeightedHomogeneous_X R (fun _ : Fin (n + 1) ↦ (1 : ℤ)) i) k

theorem coordinateChartNegativePowerFrame_cancel (s : Finset (Fin (n + 1))) (i : Fin (n + 1))
    (hi : i ∈ s) (k : ℕ)
    (x : HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) s 0) :
    (X i : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) ^ k • (coordinateChartNegativePowerFrame I s i hi k x).val = x.val :=
  Localized.NegativePowerFrames.localizedDegreeNegativePowerEquiv_cancel _ _ _ _ _ _ _ _ _ _ _

def coordinateChartNegativePowerSectionEquiv (s : Finset (Fin (n + 1))) (i : Fin (n + 1))
    (hi : i ∈ s) (k : ℕ) :
    Coefficient.AlgebraPresheaf.coefficientAlgebraSections (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
      (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s) ≃ₗ[R]
        HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) s (-(k : ℤ)) :=
  (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartSectionEquiv I s ⟨i, hi⟩).trans (coordinateChartNegativePowerFrame I s i hi k)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.NegativeChartFrames
