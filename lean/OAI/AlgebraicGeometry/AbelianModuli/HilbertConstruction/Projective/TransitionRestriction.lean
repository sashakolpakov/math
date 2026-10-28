import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SectionCover

/-! # Transition Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.TransitionRestriction

noncomputable section

/-! Projective transition units agree with the restriction of the actual singleton coordinate ratios. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem projectiveFrameRatio_eq_restriction (V : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Opens)
    (i j : Fin (n + 1)) (hi : V ≤ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i})
    (hj : V ≤ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {j}) :
    ProjectiveFrame.Ratios.projectiveFrameRatio I V i j hi hj =
      (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).presheaf.map (homOfLE hi).op
        (Coordinate.RatioSections.coordinateRatioSection I {i} i j (Finset.mem_singleton_self i)) := by
  have hV : V ≤ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i, j} := by
    rw [ProjectiveCoordinate.Cover.coordinateProjectiveChartOpen_pair]
    exact le_inf hi hj
  have hsi : i ∈ ({i, j} : Finset (Fin (n + 1))) := Finset.mem_insert_self _ _
  have hsj : j ∈ ({i, j} : Finset (Fin (n + 1))) := Finset.mem_insert_of_mem (Finset.mem_singleton_self j)
  exact (ProjectiveFrame.Ratios.projectiveFrameRatio_eq_on I V {i, j} hV i j hi hj hsi hsj).trans
    (Coordinate.RatioSubopens.coordinateRatioOn_change I V (Finset.singleton_subset_iff.mpr hsi) hV i j
      (Finset.mem_singleton_self i)).symm

theorem projectiveFrameTransition_coordinate (i j : Fin (n + 1)) :
    ((ProjectiveFrame.Transitions.projectiveFrameTransitions I).value
      ((SectionCover.projectiveCoordinateSectionCover I).overlap i j) i j inf_le_left inf_le_right).val =
      (SectionCover.projectiveCoordinateSectionCover I).transition i j :=
  projectiveFrameRatio_eq_restriction I _ i j inf_le_left inf_le_right

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.TransitionRestriction
