import Mathlib.MeasureTheory.Measure.Map

/-! # Measure Scaling Conjugacy -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.MeasureScalingConjugacy.Construction

noncomputable section

/-! Measure scaling transfers through a measurable conjugacy. -/

open _root_.MeasureTheory
open scoped ENNReal

theorem measure_scaling_of_semiconjugacy
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (e : X → Y) (he : Measurable e)
    (f : X → X) (hf : Measurable f) (g : Y → Y) (hg : Measurable g)
    (hcomp : ∀ x, g (e x) = e (f x)) (c : ℝ≥0∞) (hscale : μ.map f = c • μ) :
    (μ.map e).map g = c • μ.map e := by
  rw [Measure.map_map hg he, show g ∘ e = e ∘ f from funext hcomp,
    ← Measure.map_map he hf, hscale, Measure.map_smul _ he.aemeasurable]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.MeasureScalingConjugacy.Construction
