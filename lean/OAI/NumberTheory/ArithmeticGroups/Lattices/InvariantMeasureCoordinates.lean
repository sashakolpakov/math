import Mathlib.MeasureTheory.Group.Measure

/-! # Invariant Measure Coordinates -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantMeasureCoordinates.Construction

noncomputable section

/-! Transporting invariant measure through equivariant measurable
coordinates gives left-invariant measure on the coordinate group. -/

open _root_.MeasureTheory _root_.MeasureTheory.Measure

theorem isMulLeftInvariant_map_inverse_of_equivariant
    {H X : Type*} [Group H] [MeasurableSpace H] [MeasurableMul H] [MeasurableSpace X]
    (e : H ≃ᵐ X) (μ : Measure X) (τ : H → X → X)
    (hτ : ∀ h, MeasurePreserving (τ h) μ μ)
    (he : ∀ h x, e (h * x) = τ h (e x)) : IsMulLeftInvariant (μ.map e.symm) := by
  constructor
  intro h
  have hinv : (h * ·) ∘ e.symm = e.symm ∘ τ h := by
    funext x
    apply e.injective
    rw [Function.comp_apply, Function.comp_apply, e.apply_symm_apply, he, e.apply_symm_apply]
  rw [Measure.map_map (measurable_const_mul h) e.symm.measurable, hinv,
    ← Measure.map_map e.symm.measurable (hτ h).measurable, (hτ h).map_eq]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantMeasureCoordinates.Construction
