import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.Transitions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReindexedOpenFrameTransitions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.FromOpenFrames

/-! # Bundle -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.Bundle

noncomputable section

/-! Actual projective twisting line bundles constructed from coordinate transition units, with canonical local trivializations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def projectiveTwistingTransitions (d : ℕ) :
    OpenFrame.Transitions.OpenFrameTransitions (fun i : ULift.{u} (Fin (n + 1)) => ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i.down}) :=
  ((ProjectiveFrame.Transitions.projectiveFrameTransitions I).power d).reindex ULift.down

theorem projectiveTwistingCover (x : Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)) :
    ∃ i : ULift.{u} (Fin (n + 1)), x ∈ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i.down} := by
  have hx : x ∈ ⨆ i : Fin (n + 1), ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i} := by
    rw [ProjectiveCoordinate.Cover.coordinateProjectiveChartOpen_cover]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨ULift.up i, hi⟩

def projectiveTwistingBundle (d : ℕ) : Line.Bundles.LineBundle (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)) :=
  LineBundle.FromOpenFrames.lineBundleFromOpenFrames (projectiveTwistingTransitions I d) (projectiveTwistingCover I)

def projectiveTwistingBundle_chartIso (d : ℕ) (i : Fin (n + 1)) :
    ((projectiveTwistingBundle I d).pullback (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}).ι).sheaf ≅
      Line.Bundles.structureModule (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}).toScheme :=
  LineBundle.FromOpenFrames.lineBundleFromOpenFrames_chartIso (projectiveTwistingTransitions I d)
    (projectiveTwistingCover I) (ULift.up i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.Bundle
