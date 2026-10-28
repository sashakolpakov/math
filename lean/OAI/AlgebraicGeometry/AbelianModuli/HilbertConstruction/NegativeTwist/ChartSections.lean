import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Negative.ProjectiveTwistingBundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.NegativeChartFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.ChartValues

/-! # Chart Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.ChartSections

noncomputable section

/-! Actual sections of a negative projective twist on a coordinate chart are its negative graded localization piece. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def negativeProjectiveTwistingFrames (d : ℕ) :
    CompatibleSheaf.CompatibleSheafFrames (ProjectiveTwisting.Bundle.projectiveTwistingTransitions I d).reciprocal
      (Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I d).sheaf :=
  ConstructedCompatibleFrames.openFrameSheafFrames (ProjectiveTwisting.Bundle.projectiveTwistingTransitions I d).reciprocal

def negativeTwistChartCoefficientEquiv (d : ℕ) (s : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ s) :
    (Coefficient.ModulePresheaf.schemeModulePresheaf (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))
      (Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I d).sheaf).obj (.op (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s)) ≃ₗ[R]
        Coefficient.AlgebraPresheaf.coefficientAlgebraSections (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
          (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s) :=
  Coefficient.SectionCoordinates.coefficientFrameCoordinateEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))) _
    ((negativeProjectiveTwistingFrames I d).frame (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s) (ULift.up i)
      (ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I (Finset.singleton_subset_iff.mpr hi))).symm

def negativeTwistChartDegreeEquiv (d : ℕ) (s : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ s) :
    (Coefficient.ModulePresheaf.schemeModulePresheaf (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))
      (Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I d).sheaf).obj (.op (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s)) ≃ₗ[R]
        HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) s (-(d : ℤ)) :=
  (negativeTwistChartCoefficientEquiv I d s i hi).trans (Projective.NegativeChartFrames.coordinateChartNegativePowerSectionEquiv I s i hi d)

theorem negativeTwistingTransition_chart (d : ℕ) (s : Finset (Fin (n + 1)))
    (i j : Fin (n + 1)) (hi : i ∈ s) (hj : j ∈ s) :
    ((ProjectiveTwisting.Bundle.projectiveTwistingTransitions I d).reciprocal.value (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s)
      (ULift.up i) (ULift.up j)
      (ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I (Finset.singleton_subset_iff.mpr hi))
      (ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I (Finset.singleton_subset_iff.mpr hj))).val =
        Coordinate.RatioSections.coordinateRatioSection I s j i hj ^ d := by
  change ProjectiveFrame.Ratios.projectiveFrameRatio I (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s) j i
    (ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I (Finset.singleton_subset_iff.mpr hj))
    (ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I (Finset.singleton_subset_iff.mpr hi)) ^ d = _
  rw [ProjectiveFrame.ChartValues.projectiveFrameRatio_chart I s j i hj hi]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.ChartSections
