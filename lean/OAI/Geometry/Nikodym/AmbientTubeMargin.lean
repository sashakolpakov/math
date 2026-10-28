import OAI.Geometry.Nikodym.MetricMaximal

noncomputable section
namespace OAI.Geometry.Nikodym

open Set _root_.MeasureTheory Metric

variable {M : Type*} [MetricSpace M]

/-- A compact family of segment points has one positive ambient tube margin.
The distance here is the given ambient distance, not the path metric of the
open set. -/
theorem exists_uniform_metricTube_margin {K U : Set M}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ {I : Set M}, I ⊆ K → ∀ {δ : ℝ}, δ ≤ ε →
      metricTube δ I ⊆ U := by
  obtain ⟨ε,hε,hm⟩ := hK.exists_thickening_subset_open hU hKU
  refine ⟨ε,hε,?_⟩
  intro I hI δ hδ x hx
  apply hm
  rw [← metricTube_eq_thickening]
  obtain ⟨y,hy,hd⟩ := hx
  exact ⟨y,hI hy,hd.trans_le hδ⟩

/-- In particular, truncating small ambient tubes to the chart changes
neither their volume nor their averages. -/
theorem metricTube_inter_eq_of_margin {K U : Set M} {ε δ : ℝ}
    (hmargin : ∀ {I : Set M}, I ⊆ K → ∀ {r : ℝ}, r ≤ ε → metricTube r I ⊆ U)
    {I : Set M} (hI : I ⊆ K) (hδ : δ ≤ ε) :
    metricTube δ I ∩ U = metricTube δ I :=
  inter_eq_left.mpr (hmargin hI hδ)

variable [MeasurableSpace M]

theorem metricTubeMaximal_eq_untruncated_of_margin
    (μ : Measure M) {K U : Set M} {ε δ : ℝ}
    (hmargin : ∀ {I : Set M}, I ⊆ K → ∀ {r : ℝ}, r ≤ ε → metricTube r I ⊆ U)
    {ι : Type*} (I : M → ι → Set M) (admissible : M → ι → Prop)
    (hI : ∀ x i, admissible x i → I x i ⊆ K) (hδ : δ ≤ ε)
    (f : M → ℂ) (x : M) :
    metricTubeMaximal μ U I admissible δ f x =
      ⨆ i, ⨆ (_ : admissible x i),
        (∫⁻ y in metricTube δ (I x i), ‖f y‖ₑ ∂μ) / μ (metricTube δ (I x i)) := by
  unfold metricTubeMaximal
  apply iSup_congr
  intro i
  apply iSup_congr
  intro hi
  rw [metricTube_inter_eq_of_margin hmargin (hI x i hi) hδ]

end OAI.Geometry.Nikodym
