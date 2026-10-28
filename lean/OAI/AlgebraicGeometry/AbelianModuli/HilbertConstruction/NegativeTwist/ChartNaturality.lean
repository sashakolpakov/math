import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.ChartSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.NegativeFrameChange

/-! # Chart Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.ChartNaturality

noncomputable section

/-! The negative-twist graded chart identification is independent of the chosen inverted coordinate and commutes with actual sheaf restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem negativeTwistChartDegreeEquiv_independent (d : ℕ) (s : Finset (Fin (n + 1)))
    (i j : Fin (n + 1)) (hi : i ∈ s) (hj : j ∈ s)
    (x : Γ((Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I d).sheaf, ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s)) :
    ChartSections.negativeTwistChartDegreeEquiv I d s i hi x = ChartSections.negativeTwistChartDegreeEquiv I d s j hj x := by
  let U := ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s
  let E := ChartSections.negativeProjectiveTwistingFrames I d
  let hi' := ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I (Finset.singleton_subset_iff.mpr hi)
  let hj' := ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I (Finset.singleton_subset_iff.mpr hj)
  have hc := E.coordinate_change U (ULift.up i) (ULift.up j) hi' hj' x
  rw [ChartSections.negativeTwistingTransition_chart I d s i j hi hj] at hc
  exact (congrArg (Projective.NegativeChartFrames.coordinateChartNegativePowerSectionEquiv I s i hi d) hc).trans
    (Projective.NegativeFrameChange.coordinateChartNegativePowerSectionEquiv_change I s i j hi hj d
      ((E.frame U (ULift.up j) hj').symm x))

theorem negativeTwistChartDegreeEquiv_restriction (d : ℕ)
    {s t : Finset (Fin (n + 1))} (h : s ⊆ t) (i : Fin (n + 1)) (hi : i ∈ s)
    (x : Γ((Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I d).sheaf, ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s)) :
    (ChartSections.negativeTwistChartDegreeEquiv I d t i (h hi)
      ((Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I d).sheaf.presheaf.map
        (homOfLE (ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I h)).op x)).val =
      HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) h
        (ChartSections.negativeTwistChartDegreeEquiv I d s i hi x).val := by
  let E := ChartSections.negativeProjectiveTwistingFrames I d
  let hs := ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I (Finset.singleton_subset_iff.mpr hi)
  have hc := E.coordinate_restrict (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s)
    (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I t) (ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I h) (ULift.up i) hs x
  exact (congrArg (fun a ↦ (Projective.NegativeChartFrames.coordinateChartNegativePowerSectionEquiv I t i (h hi) d a).val) hc).trans
    (Projective.NegativeFrameRestrictions.coordinateChartNegativePowerSectionEquiv_restriction I h i hi d
      (ChartSections.negativeTwistChartCoefficientEquiv I d s i hi x))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.ChartNaturality
