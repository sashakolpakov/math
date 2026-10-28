import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient.CoordinatePullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.Bundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PulledBackFrameTransitions

/-! # Twist Pullback Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.TwistPullbackValues

noncomputable section

/-! The pulled-back degree-one twisting cocycle is evaluated by restricting the single-chart coordinate ratio. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {n : ℕ}
variable (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) (m : X ⟶ Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))

theorem projectiveTwistingPullback_value (V : X.Opens) (i j : ULift.{u} (Fin (n + 1)))
    (hi : V ≤ m ⁻¹ᵁ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i.down})
    (hj : V ≤ m ⁻¹ᵁ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {j.down}) :
    ((((ProjectiveTwisting.Bundle.projectiveTwistingTransitions I 1).pullback m).value V i j hi hj).val) =
      Open.SectionPullback.openSectionPullback m
        (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i.down} ⊓ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {j.down})
        V (le_inf hi hj)
        (ProjectiveFrame.Ratios.projectiveFrameRatio I _ i.down j.down inf_le_left inf_le_right ^ 1) := rfl

theorem projectiveTwistingPullback_singleton (V : X.Opens) (i j : ULift.{u} (Fin (n + 1)))
    (hi : V ≤ m ⁻¹ᵁ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i.down})
    (hj : V ≤ m ⁻¹ᵁ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {j.down}) :
    ((((ProjectiveTwisting.Bundle.projectiveTwistingTransitions I 1).pullback m).value V i j hi hj).val) =
      Open.SectionPullback.openSectionPullback m (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i.down}) V hi
        (Coordinate.RatioSections.coordinateRatioSection I {i.down} i.down j.down (Finset.mem_singleton_self i.down)) := by
  let U := ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i.down}
  let W := U ⊓ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {j.down}
  have he := Quotient.CoordinatePullback.projectiveFrameRatio_from_singleton I W i.down j.down inf_le_left inf_le_right
  have hr := Open.SectionPullback.openSectionPullback_restrict_source m U W inf_le_left V (le_inf hi hj)
    (Coordinate.RatioSections.coordinateRatioSection I {i.down} i.down j.down (Finset.mem_singleton_self i.down))
  have hv := projectiveTwistingPullback_value I m V i j hi hj
  exact hv.trans ((congrArg (Open.SectionPullback.openSectionPullback m W V (le_inf hi hj))
    ((pow_one _).trans he)).trans hr.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.TwistPullbackValues
