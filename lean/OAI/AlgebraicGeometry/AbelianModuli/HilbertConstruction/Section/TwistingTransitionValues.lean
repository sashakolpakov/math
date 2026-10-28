import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.QuotientCoordinatePullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.TwistPullbackValues

/-! # Twisting Transition Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.TwistingTransitionValues

noncomputable section

/-! Pulling the degree-one projective twisting cocycle back through a section-defined map gives the section-frame transition functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} {M : X.Modules} {n : ℕ} (f : X ⟶ S)
variable (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ M))
variable (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
variable (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading Γ(S, ⊤) n)) (m : X ⟶ Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))
variable (hm : m ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I = SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs)

include hm

theorem sectionQuotient_twistingTransition (V : X.Opens) (i j : ULift.{u} (Fin (n + 1)))
    (hi : V ≤ m ⁻¹ᵁ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i.down})
    (hj : V ≤ m ⁻¹ᵁ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {j.down})
    (hsi : V ≤ Ample.LineBundles.sectionNonvanishing (s i.down)) :
    ((((ProjectiveTwisting.Bundle.projectiveTwistingTransitions I 1).pullback m).value V i j hi hj).val) =
      ComponentRatios.sectionComponentRatio (s i.down) (s j.down) V hsi :=
  (Projective.TwistPullbackValues.projectiveTwistingPullback_singleton I m V i j hi hj).trans
    (QuotientCoordinatePullback.sectionQuotient_coordinate_pullback f s hs I m hm i.down j.down V hi hsi)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.TwistingTransitionValues
