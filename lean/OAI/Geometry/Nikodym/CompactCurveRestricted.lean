import OAI.Geometry.Nikodym.CompactCurveMaximal

open Set Metric _root_.MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace OAI.Geometry.Nikodym

/-- The compact-curve measurability theorem in the exact restricted metric
tube notation used by the local maximal estimate. -/
theorem measurable_metricTubeMaximal_of_compact_curves
    {M I J : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    [TopologicalSpace I] [FirstCountableTopology I] [CompactSpace I]
    [TopologicalSpace J] [CompactSpace J] [Nonempty J]
    (μ : Measure M) (S : Set M) [IsFiniteMeasure (μ.restrict S)]
    (γ : (M × I) × J → M) (hγ : Continuous γ) (δ : ℝ)
    (hz : ∀ p,(μ.restrict S) {x | infDist x (range (fun t => γ (p,t)))=δ}=0)
    (hp : ∀ p,(μ.restrict S) (metricTube δ (range (fun t => γ (p,t)))) ≠ 0)
    (A : Set (M × I)) (hA : IsClosed A)
    (f : M → ℂ) (hf : Integrable f (μ.restrict S)) :
    Measurable (metricTubeMaximal μ S (fun x i => range (fun t => γ ((x,i),t)))
      (fun x i => (x,i)∈A) δ f) := by
  have hc := measurable_compact_curve_maximal (μ.restrict S) γ hγ δ hz hp A hA f hf
  have he : (fun p => ⨆ i,⨆ (_ : (p,i)∈A),
      (∫⁻ x in metricTube δ (range (fun t => γ ((p,i),t))),‖f x‖ₑ ∂μ.restrict S) /
        (μ.restrict S) (metricTube δ (range (fun t => γ ((p,i),t))))) =
      metricTubeMaximal μ S (fun x i => range (fun t => γ ((x,i),t)))
        (fun x i => (x,i)∈A) δ f := by
    funext p
    apply iSup_congr
    intro i
    apply iSup_congr
    intro hi
    have hT : MeasurableSet (metricTube δ (range (fun t => γ ((p,i),t)))) := by
      rw [metricTube_eq_thickening]
      exact Metric.isOpen_thickening.measurableSet
    rw [Measure.restrict_restrict hT,Measure.restrict_apply hT]
  rwa [he] at hc

end OAI.Geometry.Nikodym
