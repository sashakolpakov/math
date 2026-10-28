import OAI.Geometry.Nikodym.SublevelMaximal
import OAI.Geometry.Nikodym.CompactCurveDistance
import OAI.Geometry.Nikodym.CurveDistanceSlice
import OAI.Geometry.Nikodym.MetricMaximal

open Set Filter Metric _root_.MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace OAI.Geometry.Nikodym

/-- Closed incidence for a compact, continuously parameterized family of
curves. The curve need not have a unique parameter at the observation point. -/
theorem isClosed_compact_curve_incidence
    {X I J : Type*} [MetricSpace X] [TopologicalSpace I] [TopologicalSpace J]
    [CompactSpace J] (γ : (X × I) × J → X) (hγ : Continuous γ) :
    IsClosed {q : X × I | q.1 ∈ range (fun t => γ (q,t))} := by
  have hc : IsClosed {q : (X × I) × J | γ q=q.1.1} :=
    isClosed_eq hγ continuous_fst.fst
  have he : {q : X × I | q.1 ∈ range (fun t => γ (q,t))} =
      Prod.fst '' {q : (X × I) × J | γ q=q.1.1} := by
    ext q
    constructor
    · rintro ⟨t,ht⟩
      exact ⟨(q,t),ht,rfl⟩
    · rintro ⟨⟨q',t⟩,ht,hq⟩
      change q'=q at hq
      subst q'
      exact ⟨t,ht⟩
  rw [he]
  exact isClosedMap_fst_of_compactSpace _ hc

/-- The actual metric-tube supremum is measurable for compact curve
parameters and closed admissibility. Null distance levels, rather than a
measurability assumption on the supremum, are the geometric input. -/
theorem measurable_compact_curve_maximal
    {P I J X : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    [MeasurableSpace P] [BorelSpace P]
    [TopologicalSpace I] [FirstCountableTopology I] [CompactSpace I]
    [TopologicalSpace J] [CompactSpace J] [Nonempty J]
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (γ : (P × I) × J → X) (hγ : Continuous γ) (δ : ℝ)
    (hz : ∀ p,μ {x | infDist x (range (fun t => γ (p,t)))=δ}=0)
    (hp : ∀ p,μ (metricTube δ (range (fun t => γ (p,t)))) ≠ 0)
    (A : Set (P × I)) (hA : IsClosed A)
    (f : X → ℂ) (hf : Integrable f μ) :
    Measurable (fun p => ⨆ i,⨆ (_ : (p,i)∈A),
      (∫⁻ x in metricTube δ (range (fun t => γ ((p,i),t))),‖f x‖ₑ ∂μ) /
        μ (metricTube δ (range (fun t => γ ((p,i),t))))) := by
  let d : P × I → X → ℝ := fun p x => infDist x (range (fun t => γ (p,t)))
  have hd (x : X) : Continuous (fun p => d p x) := continuous_infDist_range_parameter γ hγ x
  have hm (p : P × I) : Measurable (d p) := (continuous_infDist_pt _).measurable
  have hp' (p : P × I) : μ {x | d p x<δ} ≠ 0 := by
    simpa only [metricTube_eq_infDist_sublevel (range_nonempty _)] using hp p
  have hH : AEMeasurable (fun x => ‖f x‖ₑ) μ := hf.aestronglyMeasurable.enorm
  have hc := measurable_compact_strict_sublevel_maximal μ d δ hd hm hz hp' A hA
    (fun x => ‖f x‖ₑ) hH hf.hasFiniteIntegral
  convert hc using 1
  funext p
  apply iSup_congr
  intro i
  apply iSup_congr
  intro hi
  rw [metricTube_eq_infDist_sublevel (range_nonempty _)]

end OAI.Geometry.Nikodym
