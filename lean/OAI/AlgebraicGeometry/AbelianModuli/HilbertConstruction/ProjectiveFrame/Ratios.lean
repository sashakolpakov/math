import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.RatioSubopens
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CommonCoordinateOpen

/-! # Ratios -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.Ratios

noncomputable section

/-! Projective frame transition functions on every common subopen of two standard charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def projectiveFrameRatio (V : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Opens) (i j : Fin (n + 1))
    (hi : V ≤ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}) (hj : V ≤ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {j}) :
    Γ(Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I), V) :=
  Coordinate.RatioSubopens.coordinateRatioOn I V {i, j} (by rw [ProjectiveCoordinate.Cover.coordinateProjectiveChartOpen_pair]; exact le_inf hi hj)
    i j (Finset.mem_insert_self _ _)

theorem projectiveFrameRatio_eq_on (V : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Opens)
    (s : Finset (Fin (n + 1))) (hV : V ≤ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s)
    (i j : Fin (n + 1)) (hi : V ≤ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i})
    (hj : V ≤ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {j}) (hsi : i ∈ s) (hsj : j ∈ s) :
    projectiveFrameRatio I V i j hi hj = Coordinate.RatioSubopens.coordinateRatioOn I V s hV i j hsi := by
  have h : ({i, j} : Finset (Fin (n + 1))) ⊆ s := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hsi
    · exact Finset.mem_singleton.mp ha ▸ hsj
  exact Coordinate.RatioSubopens.coordinateRatioOn_change I V h hV i j (Finset.mem_insert_self _ _)

theorem projectiveFrameRatio_self (V : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Opens) (i : Fin (n + 1))
    (hi : V ≤ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}) : projectiveFrameRatio I V i i hi hi = 1 :=
  Coordinate.RatioSubopens.coordinateRatioOn_self I V _ _ i _

theorem projectiveFrameRatio_restrict (V W : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Opens) (h : W ≤ V)
    (i j : Fin (n + 1)) (hi : V ≤ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i})
    (hj : V ≤ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {j}) :
    (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).presheaf.map (homOfLE h).op (projectiveFrameRatio I V i j hi hj) =
      projectiveFrameRatio I W i j (h.trans hi) (h.trans hj) :=
  Coordinate.RatioSubopens.coordinateRatioOn_restrict I V W h _ _ i j _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.Ratios
