import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.Bundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.TwistFrameCompatibility
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.CoefficientSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LiftedFrameCompatibility

/-! # Twist Global Tuples -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.TwistGlobalTuples

noncomputable section

/-! Actual global sections of the projective twist inject into standard chart coefficients, with image given precisely by the homogeneous transition equations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def projectiveTwistGlobalTupleMap (d : ℕ) :
    (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))).obj
      (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf →ₗ[R]
    ((i : Fin (n + 1)) → Coefficient.AlgebraPresheaf.coefficientAlgebraSections
      (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))) (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i})) :=
  (LiftedFrameCompatibility.coefficientTupleULiftEquiv (U := fun i : Fin (n + 1) => ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i})
    (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))).toLinearMap.comp
    (OpenFrame.CoefficientSections.openFrameCoefficientGlobalTupleMap (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
      (ProjectiveTwisting.Bundle.projectiveTwistingTransitions I d))

theorem projectiveTwistGlobalTupleMap_injective (d : ℕ) : Function.Injective (projectiveTwistGlobalTupleMap I d) :=
  (LiftedFrameCompatibility.coefficientTupleULiftEquiv (U := fun i : Fin (n + 1) => ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i})
    (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))).injective.comp
    (OpenFrame.CoefficientSections.openFrameCoefficientGlobalTupleMap_injective _ (ProjectiveTwisting.Bundle.projectiveTwistingTransitions I d))

theorem projectiveTwistGlobalTupleMap_range (d : ℕ)
    (x : (i : Fin (n + 1)) → Coefficient.AlgebraPresheaf.coefficientAlgebraSections
      (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))) (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i})) :
    (∃ s, projectiveTwistGlobalTupleMap I d s = x) ↔ TwistCechKernel.CoordinateTwistCompatible I d x := by
  let f := Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))
  let D := (ProjectiveFrame.Transitions.projectiveFrameTransitions I).power d
  let e := LiftedFrameCompatibility.coefficientTupleULiftEquiv (U := fun i : Fin (n + 1) => ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}) f
  constructor
  · rintro ⟨s, rfl⟩
    have h := (OpenFrame.CoefficientSections.openFrameCoefficientGlobalTupleMap_range f (ProjectiveTwisting.Bundle.projectiveTwistingTransitions I d)
      (OpenFrame.CoefficientSections.openFrameCoefficientGlobalTupleMap f (ProjectiveTwisting.Bundle.projectiveTwistingTransitions I d) s)).mp ⟨s, rfl⟩
    exact (TwistFrameCompatibility.coordinateTwistCompatible_iff_frame I d _).mpr ((LiftedFrameCompatibility.frameCompatible_ulift D _).mp h)
  · intro hx
    have h : Frame.TransitionEquations.FrameCompatible (ProjectiveTwisting.Bundle.projectiveTwistingTransitions I d) (e.symm x) :=
      (LiftedFrameCompatibility.frameCompatible_ulift D _).mpr ((TwistFrameCompatibility.coordinateTwistCompatible_iff_frame I d x).mp hx)
    obtain ⟨s, hs⟩ := (OpenFrame.CoefficientSections.openFrameCoefficientGlobalTupleMap_range f (ProjectiveTwisting.Bundle.projectiveTwistingTransitions I d) (e.symm x)).mpr h
    exact ⟨s, (congrArg e hs).trans (e.apply_symm_apply x)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.TwistGlobalTuples
