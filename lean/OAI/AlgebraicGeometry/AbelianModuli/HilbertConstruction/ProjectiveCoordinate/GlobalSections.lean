import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.Bundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.CoordinateSections

/-! # Global Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveCoordinate.GlobalSections

noncomputable section

/-! Homogeneous coordinates define actual global sections of the projective twisting line bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def projectiveCoordinateTuple (j : Fin (n + 1)) :
    OpenFrame.GlobalTuples.OpenFrameGlobalTuple (fun i : ULift.{u} (Fin (n + 1)) => ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i.down}) :=
  fun i => Coordinate.RatioSections.coordinateRatioSection I {i.down} i.down j (Finset.mem_singleton_self _)

theorem projectiveCoordinateTuple_compatible (j : Fin (n + 1)) :
    Frame.TransitionEquations.FrameCompatible (ProjectiveTwisting.Bundle.projectiveTwistingTransitions I 1) (projectiveCoordinateTuple I j) := by
  intro i k
  let V := ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i.down} ⊓ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {k.down}
  let a : Finset (Fin (n + 1)) := {i.down, k.down}
  have hV : V ≤ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I a := by
    rw [Cover.coordinateProjectiveChartOpen_pair]
  have hi : ({i.down} : Finset (Fin (n + 1))) ⊆ a := by simp [a]
  have hk : ({k.down} : Finset (Fin (n + 1))) ⊆ a := by simp [a]
  change Coordinate.RatioSubopens.coordinateRatioOn I V {i.down} inf_le_left i.down j _ =
    ProjectiveFrame.Ratios.projectiveFrameRatio I V i.down k.down inf_le_left inf_le_right ^ 1 *
      Coordinate.RatioSubopens.coordinateRatioOn I V {k.down} inf_le_right k.down j _
  rw [pow_one,
    ProjectiveFrame.Ratios.projectiveFrameRatio_eq_on I V a hV i.down k.down inf_le_left inf_le_right (by simp [a]) (by simp [a]),
    Coordinate.RatioSubopens.coordinateRatioOn_change I V hi hV i.down j,
    Coordinate.RatioSubopens.coordinateRatioOn_change I V hk hV k.down j]
  exact (Coordinate.RatioSubopens.coordinateRatioOn_comp I V a hV i.down k.down j (by simp [a]) (by simp [a])).symm

def projectiveCoordinateSection (j : Fin (n + 1)) :
    Line.Bundles.structureModule (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)) ⟶ (ProjectiveTwisting.Bundle.projectiveTwistingBundle I 1).sheaf :=
  OpenFrame.CoordinateSections.openFrameSectionOfCompatible (ProjectiveTwisting.Bundle.projectiveTwistingTransitions I 1)
    (projectiveCoordinateTuple I j) (projectiveCoordinateTuple_compatible I j)

theorem projectiveCoordinateSection_tuple (j : Fin (n + 1)) :
    OpenFrame.CoefficientSections.openFrameGlobalTupleMap (ProjectiveTwisting.Bundle.projectiveTwistingTransitions I 1)
      (Global.Sections.moduleSectionHomEquiv (ProjectiveTwisting.Bundle.projectiveTwistingBundle I 1).sheaf (projectiveCoordinateSection I j)) =
        projectiveCoordinateTuple I j :=
  OpenFrame.CoordinateSections.openFrameSectionOfCompatible_tuple (ProjectiveTwisting.Bundle.projectiveTwistingTransitions I 1)
    (projectiveCoordinateTuple I j) (projectiveCoordinateTuple_compatible I j)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveCoordinate.GlobalSections
