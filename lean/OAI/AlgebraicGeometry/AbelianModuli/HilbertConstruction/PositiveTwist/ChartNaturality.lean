import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PositiveTwist.ChartSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PowerFrameChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PowerFrameRestrictions

/-! # Chart Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PositiveTwist.ChartNaturality

noncomputable section

/-! The nonnegative-twist graded chart identification is independent of the chosen inverted coordinate and commutes with actual sheaf restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem positiveTwistChartDegreeEquiv_independent (d : ℕ) (s : Finset (Fin (n + 1)))
    (i j : Fin (n + 1)) (hi : i ∈ s) (hj : j ∈ s)
    (x : Γ((ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf, ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s)) :
    ChartSections.positiveTwistChartDegreeEquiv I d s i hi x = ChartSections.positiveTwistChartDegreeEquiv I d s j hj x := by
  let U := ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s
  let E := ChartSections.positiveProjectiveTwistingFrames I d
  let hi' := ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I (Finset.singleton_subset_iff.mpr hi)
  let hj' := ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I (Finset.singleton_subset_iff.mpr hj)
  have hc := E.coordinate_change U (ULift.up i) (ULift.up j) hi' hj' x
  rw [ChartSections.positiveTwistingTransition_chart I d s i j hi hj] at hc
  exact (congrArg (ProjectiveChart.PowerFrames.coordinateChartPowerSectionEquiv I s i hi d) hc).trans
    (Projective.PowerFrameChange.coordinateChartPowerSectionEquiv_change I s i j hi hj d
      ((E.frame U (ULift.up j) hj').symm x))

theorem positiveTwistChartDegreeEquiv_restriction (d : ℕ)
    {s t : Finset (Fin (n + 1))} (h : s ⊆ t) (i : Fin (n + 1)) (hi : i ∈ s)
    (x : Γ((ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf, ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s)) :
    (ChartSections.positiveTwistChartDegreeEquiv I d t i (h hi)
      ((ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf.presheaf.map
        (homOfLE (ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I h)).op x)).val =
      HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) h
        (ChartSections.positiveTwistChartDegreeEquiv I d s i hi x).val := by
  let E := ChartSections.positiveProjectiveTwistingFrames I d
  let hs := ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I (Finset.singleton_subset_iff.mpr hi)
  have hc := E.coordinate_restrict (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s)
    (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I t) (ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I h) (ULift.up i) hs x
  exact (congrArg (fun a ↦ (ProjectiveChart.PowerFrames.coordinateChartPowerSectionEquiv I t i (h hi) d a).val) hc).trans
    (Projective.PowerFrameRestrictions.coordinateChartPowerSectionEquiv_restriction I h i hi d
      (ChartSections.positiveTwistChartCoefficientEquiv I d s i hi x))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PositiveTwist.ChartNaturality
