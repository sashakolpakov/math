import OAI.Geometry.Nikodym.TubeMeasurability

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Geometry.Nikodym

/-- Measurability of the genuine local metric maximal function from its
geometric parametrization. The input is only measurable on the chart, and the
metric tubes are always intersected with that chart in the actual averages. -/
theorem measurable_metricTubeMaximal
    {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] {ι : Type*}
    (μ : Measure M) {S : Set M} (_ : MeasurableSet S)
    (I : M → ι → Set M) (admissible : M → ι → Prop) (δ : ℝ)
    (hopen : ∀ i y,IsOpen {x | y∈metricTube δ (I x i)})
    (hvol : ∀ i,Continuous (fun x => μ (metricTube δ (I x i) ∩ S)))
    (hadm : ∀ i,IsOpen {x | admissible x i})
    (f : M → ℂ) (hf : AEStronglyMeasurable f (μ.restrict S)) :
    Measurable (metricTubeMaximal μ S I admissible δ f) := by
  have hT (x : M) (i : ι) : MeasurableSet (metricTube δ (I x i)) := by
    rw [metricTube_eq_thickening]
    exact Metric.isOpen_thickening.measurableSet
  have hv (i : ι) : Continuous (fun x => (μ.restrict S) (metricTube δ (I x i))) := by
    simpa only [Measure.restrict_apply (hT _ _)] using hvol i
  have H := measurable_admissible_tube_sup (μ.restrict S)
    (fun x i => metricTube δ (I x i)) admissible hT hopen hv hadm f hf
  convert H using 1
  funext x
  apply iSup_congr
  intro i
  apply iSup_congr
  intro hi
  rw [Measure.restrict_apply (hT x i),Measure.restrict_restrict (hT x i)]

end OAI.Geometry.Nikodym
