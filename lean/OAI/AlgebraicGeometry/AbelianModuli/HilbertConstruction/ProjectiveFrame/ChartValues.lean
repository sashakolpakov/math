import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.Transitions

/-! # Chart Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.ChartValues

noncomputable section

/-! The projective transition on a coordinate chart is its actual homogeneous ratio section. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem projectiveFrameRatio_chart (s : Finset (Fin (n + 1))) (i j : Fin (n + 1))
    (hi : i ∈ s) (hj : j ∈ s) :
    Ratios.projectiveFrameRatio I (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s) i j
      (ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I (Finset.singleton_subset_iff.mpr hi))
      (ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I (Finset.singleton_subset_iff.mpr hj)) =
      Coordinate.RatioSections.coordinateRatioSection I s i j hi := by
  have he := Ratios.projectiveFrameRatio_eq_on I (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s) s le_rfl i j
    (ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I (Finset.singleton_subset_iff.mpr hi))
    (ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I (Finset.singleton_subset_iff.mpr hj)) hi hj
  exact he.trans (ConcreteCategory.congr_hom ((Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).presheaf.map_id
    (.op (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s))) (Coordinate.RatioSections.coordinateRatioSection I s i j hi))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.ChartValues
