import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Continuous Density -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.ContinuousDensity.Construction

noncomputable section

/-! A continuous strictly positive real density preserves local
finiteness and positivity on open sets. -/

open _root_.MeasureTheory _root_.MeasureTheory.Measure
open scoped ENNReal

theorem isOpenPosMeasure_withDensity_positive
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsOpenPosMeasure μ] (f : X → ℝ≥0∞)
    (hf : Measurable f) (hpos : ∀ x, f x ≠ 0) : IsOpenPosMeasure (μ.withDensity f) := by
  constructor
  intro U hU hUn hz
  have hz' := (withDensity_apply_eq_zero hf).mp hz
  apply hU.measure_ne_zero μ hUn
  have hset : {x | f x ≠ 0} = Set.univ := Set.eq_univ_of_forall hpos
  rwa [hset, Set.univ_inter] at hz'

theorem continuous_positive_density_finite_on_compacts
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsLocallyFiniteMeasure μ] (f : X → ℝ) (hf : Continuous f) :
    IsFiniteMeasureOnCompacts (μ.withDensity (fun x => ENNReal.ofReal (f x))) := by
  let := IsLocallyFiniteMeasure.withDensity_ofReal (μ := μ) hf
  infer_instance

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.ContinuousDensity.Construction
