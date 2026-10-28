import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.Ratios
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.Transitions

/-! # Transitions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.Transitions

noncomputable section

/-! The projective coordinate ratios form an actual regular-function transition cocycle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem projectiveFrameRatio_comp (V : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Opens) (i j k : Fin (n + 1))
    (hi : V ≤ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}) (hj : V ≤ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {j})
    (hk : V ≤ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {k}) :
    Ratios.projectiveFrameRatio I V i j hi hj * Ratios.projectiveFrameRatio I V j k hj hk =
      Ratios.projectiveFrameRatio I V i k hi hk := by
  let s : Finset (Fin (n + 1)) := {i, j, k}
  have hsi : i ∈ s := by simp [s]
  have hsj : j ∈ s := by simp [s]
  have hsk : k ∈ s := by simp [s]
  have hV : V ≤ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s := by
    apply Projective.CommonCoordinateOpen.le_coordinateProjectiveChartOpen
    intro a ha
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact hi
    · exact hj
    · exact hk
  rw [Ratios.projectiveFrameRatio_eq_on I V s hV i j hi hj hsi hsj,
    Ratios.projectiveFrameRatio_eq_on I V s hV j k hj hk hsj hsk,
    Ratios.projectiveFrameRatio_eq_on I V s hV i k hi hk hsi hsk]
  exact Coordinate.RatioSubopens.coordinateRatioOn_comp I V s hV i j k hsi hsj

def projectiveFrameTransitionUnit (V : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Opens) (i j : Fin (n + 1))
    (hi : V ≤ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}) (hj : V ≤ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {j}) :
    Γ(Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I), V)ˣ where
  val := Ratios.projectiveFrameRatio I V i j hi hj
  inv := Ratios.projectiveFrameRatio I V j i hj hi
  val_inv := (projectiveFrameRatio_comp I V i j i hi hj hi).trans (Ratios.projectiveFrameRatio_self I V i hi)
  inv_val := (projectiveFrameRatio_comp I V j i j hj hi hj).trans (Ratios.projectiveFrameRatio_self I V j hj)

def projectiveFrameTransitions :
    OpenFrame.Transitions.OpenFrameTransitions (fun i : Fin (n + 1) => ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}) where
  value := projectiveFrameTransitionUnit I
  restrict := Ratios.projectiveFrameRatio_restrict I
  self V i hi := Units.ext (Ratios.projectiveFrameRatio_self I V i hi)
  comp V i j k hi hj hk := Units.ext (projectiveFrameRatio_comp I V i j k hi hj hk)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.Transitions
