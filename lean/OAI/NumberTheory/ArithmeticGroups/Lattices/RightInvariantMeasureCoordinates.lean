import Mathlib.MeasureTheory.Group.Measure

/-! # Right Invariant Measure Coordinates -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.RightInvariantMeasureCoordinates.Construction

noncomputable section

/-! Coordinate transformations that preserve a source measure and
represent right translations give a right-invariant image measure. -/

open _root_.MeasureTheory _root_.MeasureTheory.Measure

theorem isMulRightInvariant_map_of_coordinates
    {X G : Type*} [MeasurableSpace X] [Group G] [MeasurableSpace G] [MeasurableMul G]
    (e : X ≃ᵐ G) (μ : Measure X) (τ : G → X → X)
    (hτ : ∀ g, MeasurePreserving (τ g) μ μ)
    (he : ∀ g x, e (τ g x) = e x * g) : IsMulRightInvariant (μ.map e) := by
  constructor
  intro g
  have hcomp : (· * g) ∘ e = e ∘ τ g := funext (fun x => (he g x).symm)
  rw [Measure.map_map (measurable_mul_const g) e.measurable, hcomp,
    ← Measure.map_map e.measurable (hτ g).measurable, (hτ g).map_eq]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.RightInvariantMeasureCoordinates.Construction
