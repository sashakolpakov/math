import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Order.Disjointed

/-! # Measure Gluing -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MeasureGluing.CM.Construction

noncomputable section

/-! Compatible local Borel measures glue along a countable ordered cover.
The construction uses its actual measurable disjoint refinement. -/

open _root_.MeasureTheory Set

variable {X ι : Type*} [MeasurableSpace X] [Countable ι]
  [LinearOrder ι] [LocallyFiniteOrderBot ι]

def gluedChartMeasure (U : ι → Set X) (μ : ι → Measure X) : Measure X :=
  Measure.sum (fun i => (μ i).restrict (disjointed U i))

theorem disjointed_cover_measurable (U : ι → Set X) (hU : ∀ i, MeasurableSet (U i)) (i : ι) :
    MeasurableSet (disjointed U i) := by
  rw [disjointed_eq_inter_compl]
  exact (hU i).inter (MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun _ => (hU j).compl)))

theorem gluedChartMeasure_restrict (U : ι → Set X) (μ : ι → Measure X)
    (hU : ∀ i, MeasurableSet (U i)) (hcover : ⋃ i, U i = univ)
    (hcompat : ∀ i j, (μ i).restrict (U i ∩ U j) = (μ j).restrict (U i ∩ U j))
    (j : ι) : (gluedChartMeasure U μ).restrict (U j) = (μ j).restrict (U j) := by
  have hpiece (i : ι) : ((μ i).restrict (disjointed U i)).restrict (U j) =
      ((μ j).restrict (disjointed U i)).restrict (U j) := by
    rw [Measure.restrict_restrict (hU j), Measure.restrict_restrict (hU j)]
    apply Measure.restrict_congr_mono _ (hcompat i j)
    exact fun x hx => ⟨disjointed_subset U i hx.2, hx.1⟩
  have hsum : Measure.sum (fun i => (μ j).restrict (disjointed U i)) = μ j := by
    rw [← Measure.restrict_iUnion (disjoint_disjointed U) (disjointed_cover_measurable U hU),
      iUnion_disjointed, hcover, Measure.restrict_univ]
  rw [gluedChartMeasure, Measure.restrict_sum _ (hU j)]
  have heq : (fun i => ((μ i).restrict (disjointed U i)).restrict (U j)) =
      (fun i => ((μ j).restrict (disjointed U i)).restrict (U j)) := funext hpiece
  rw [heq, ← Measure.restrict_sum _ (hU j), hsum]

/-- Local measures supported in the members of a cover, and agreeing on
overlaps, determine one and only one global measure. -/
theorem compatible_measures_existsUnique (U : ι → Set X) (μ : ι → Measure X)
    (hU : ∀ i, MeasurableSet (U i)) (hcover : ⋃ i, U i = univ)
    (hsupport : ∀ i, (μ i).restrict (U i) = μ i)
    (hcompat : ∀ i j, (μ i).restrict (U i ∩ U j) = (μ j).restrict (U i ∩ U j)) :
    ∃! ν : Measure X, ∀ i, ν.restrict (U i) = μ i := by
  refine ⟨gluedChartMeasure U μ, ?_, ?_⟩
  · intro i
    rw [gluedChartMeasure_restrict U μ hU hcover hcompat i, hsupport i]
  · intro ν hν
    apply Measure.ext_of_iUnion_eq_univ hcover
    intro i
    rw [hν i, gluedChartMeasure_restrict U μ hU hcover hcompat i, hsupport i]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MeasureGluing.CM.Construction
