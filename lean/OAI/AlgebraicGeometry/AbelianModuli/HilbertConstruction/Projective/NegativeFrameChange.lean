import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.NegativeFrameRestrictions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PowerFrameChange

/-! # Negative Frame Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.NegativeFrameChange

noncomputable section

/-! Negative chart frames change by reciprocal powers of the actual coordinate ratios. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem coordinateChartNegativePowerSectionEquiv_change
    (s : Finset (Fin (n + 1))) (i j : Fin (n + 1)) (hi : i ∈ s) (hj : j ∈ s) (d : ℕ)
    (x : Γ(Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I), ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s)) :
    NegativeChartFrames.coordinateChartNegativePowerSectionEquiv I s i hi d (Coordinate.RatioSections.coordinateRatioSection I s j i hj ^ d * x) =
      NegativeChartFrames.coordinateChartNegativePowerSectionEquiv I s j hj d x := by
  apply Subtype.ext
  apply NegativeFrameRestrictions.coordinateChartPower_smul_injective I s i hi d
  apply NegativeFrameRestrictions.coordinateChartPower_smul_injective I s j hj d
  have hi' := NegativeChartFrames.coordinateChartNegativePowerFrame_cancel I s i hi d
    (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartSectionEquiv I s ⟨i, hi⟩ (Coordinate.RatioSections.coordinateRatioSection I s j i hj ^ d * x))
  have hj' := NegativeChartFrames.coordinateChartNegativePowerFrame_cancel I s j hj d
    (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartSectionEquiv I s ⟨j, hj⟩ x)
  have hchange := congrArg Subtype.val (PowerFrameChange.coordinateChartPowerSectionEquiv_change I s j i hj hi d x)
  change (X j : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) ^ d •
      ((X i : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) ^ d • (NegativeChartFrames.coordinateChartNegativePowerFrame I s i hi d
        (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartSectionEquiv I s ⟨i, hi⟩ (Coordinate.RatioSections.coordinateRatioSection I s j i hj ^ d * x))).val) =
    (X j : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) ^ d •
      ((X i : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) ^ d • (NegativeChartFrames.coordinateChartNegativePowerFrame I s j hj d
        (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartSectionEquiv I s ⟨j, hj⟩ x)).val)
  rw [hi', smul_comm ((X j : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) ^ d) ((X i : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) ^ d), hj']
  exact hchange

theorem coordinateChartNegativePowerSectionEquiv_eq_iff
    (s : Finset (Fin (n + 1))) (i j : Fin (n + 1)) (hi : i ∈ s) (hj : j ∈ s) (d : ℕ)
    (x y : Γ(Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I), ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s)) :
    NegativeChartFrames.coordinateChartNegativePowerSectionEquiv I s i hi d x =
      NegativeChartFrames.coordinateChartNegativePowerSectionEquiv I s j hj d y ↔
        x = Coordinate.RatioSections.coordinateRatioSection I s j i hj ^ d * y := by
  rw [← coordinateChartNegativePowerSectionEquiv_change I s i j hi hj d y]
  exact (NegativeChartFrames.coordinateChartNegativePowerSectionEquiv I s i hi d).injective.eq_iff

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.NegativeFrameChange
