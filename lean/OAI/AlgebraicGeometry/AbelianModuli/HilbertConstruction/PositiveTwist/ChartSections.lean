import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.Bundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.PowerFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.ChartValues

/-! # Chart Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PositiveTwist.ChartSections

noncomputable section

/-! Actual sections of a nonnegative projective twist on a coordinate chart are its nonnegative graded localization piece. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def positiveProjectiveTwistingFrames (d : ℕ) :
    CompatibleSheaf.CompatibleSheafFrames (ProjectiveTwisting.Bundle.projectiveTwistingTransitions I d)
      (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf :=
  ConstructedCompatibleFrames.openFrameSheafFrames (ProjectiveTwisting.Bundle.projectiveTwistingTransitions I d)

def positiveTwistChartCoefficientEquiv (d : ℕ) (s : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ s) :
    (Coefficient.ModulePresheaf.schemeModulePresheaf (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))
      (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf).obj (.op (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s)) ≃ₗ[R]
        Coefficient.AlgebraPresheaf.coefficientAlgebraSections (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
          (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s) :=
  Coefficient.SectionCoordinates.coefficientFrameCoordinateEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))) _
    ((positiveProjectiveTwistingFrames I d).frame (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s) (ULift.up i)
      (ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I (Finset.singleton_subset_iff.mpr hi))).symm

def positiveTwistChartDegreeEquiv (d : ℕ) (s : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ s) :
    (Coefficient.ModulePresheaf.schemeModulePresheaf (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))
      (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf).obj (.op (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s)) ≃ₗ[R]
        HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) s (d : ℤ) :=
  (positiveTwistChartCoefficientEquiv I d s i hi).trans (ProjectiveChart.PowerFrames.coordinateChartPowerSectionEquiv I s i hi d)

theorem positiveTwistingTransition_chart (d : ℕ) (s : Finset (Fin (n + 1)))
    (i j : Fin (n + 1)) (hi : i ∈ s) (hj : j ∈ s) :
    ((ProjectiveTwisting.Bundle.projectiveTwistingTransitions I d).value (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s)
      (ULift.up i) (ULift.up j)
      (ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I (Finset.singleton_subset_iff.mpr hi))
      (ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I (Finset.singleton_subset_iff.mpr hj))).val =
        Coordinate.RatioSections.coordinateRatioSection I s i j hi ^ d := by
  change ProjectiveFrame.Ratios.projectiveFrameRatio I (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s) i j
    (ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I (Finset.singleton_subset_iff.mpr hi))
    (ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I (Finset.singleton_subset_iff.mpr hj)) ^ d = _
  rw [ProjectiveFrame.ChartValues.projectiveFrameRatio_chart I s i j hi hj]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PositiveTwist.ChartSections
