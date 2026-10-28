import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.TwistCechKernel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.ChartValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReindexedOpenFrameTransitions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.TransitionEquations

/-! # Twist Frame Compatibility -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.TwistFrameCompatibility

noncomputable section

/-! Homogeneous coordinate compatibility is the actual frame-cocycle compatibility of the constructed projective twist. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem coordinateTwistCompatible_iff_frame (d : ℕ)
    (x : (i : Fin (n + 1)) → Coefficient.AlgebraPresheaf.coefficientAlgebraSections
      (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))) (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i})) :
    TwistCechKernel.CoordinateTwistCompatible I d x ↔ Frame.TransitionEquations.FrameCompatible ((ProjectiveFrame.Transitions.projectiveFrameTransitions I).power d) x := by
  unfold TwistCechKernel.CoordinateTwistCompatible Frame.TransitionEquations.FrameCompatible
  apply forall₂_congr
  intro i j
  let hL : ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i, j} ≤ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i} := ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I
    (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self i {j}))
  let hR : ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i, j} ≤ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {j} := ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I
    (Finset.singleton_subset_iff.mpr (Finset.mem_insert_of_mem (Finset.mem_singleton_self j)))
  have he := Frame.TransitionEquations.frameTransitionEquation_of_open_eq ((ProjectiveFrame.Transitions.projectiveFrameTransitions I).power d) i j
    hL hR inf_le_left inf_le_right (ProjectiveCoordinate.Cover.coordinateProjectiveChartOpen_pair I i j) (x i) (x j)
  refine Iff.trans ?_ he
  change (_ = _) ↔ (_ = ProjectiveFrame.Ratios.projectiveFrameRatio I (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i, j}) i j hL hR ^ d * _)
  rw [ProjectiveFrame.ChartValues.projectiveFrameRatio_chart I {i, j} i j (Finset.mem_insert_self i {j})
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self j))]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.TwistFrameCompatibility
