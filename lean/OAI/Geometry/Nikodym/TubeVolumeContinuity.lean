import OAI.Geometry.Nikodym.TubeMeasurability

open _root_.MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace OAI.Geometry.Nikodym

/-- Finite-volume tube families have continuous volume when membership is
locally stable away from a null boundary. -/
theorem continuous_volume_of_ae_stable_membership
    {P X : Type*} [TopologicalSpace P] [FirstCountableTopology P] [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (T : P → Set X)
    (hT : ∀ p,MeasurableSet (T p))
    (hstable : ∀ p,∀ᵐ x ∂μ,∀ᶠ q in 𝓝 p,(x∈T q ↔ x∈T p)) :
    Continuous (fun p => μ (T p)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  change Tendsto (fun q => μ (T q)) (𝓝 p) (𝓝 (μ (T p)))
  let F : P → X → ℝ≥0∞ := fun q => (T q).indicator (fun _ => 1)
  have H := tendsto_lintegral_filter_of_dominated_convergence
    (μ := μ) (l := 𝓝 p) (F := F) (f := F p) (fun _ => 1)
    (Eventually.of_forall fun q => measurable_const.indicator (hT q))
    (Eventually.of_forall fun q => Eventually.of_forall fun x => by
      by_cases hx : x∈T q <;> simp [F,hx])
    (by simp)
    ((hstable p).mono fun x hx => by
      apply tendsto_const_nhds.congr'
      filter_upwards [hx] with q hq
      by_cases hxp : x∈T p
      · simp only [F,indicator_of_mem hxp,indicator_of_mem (hq.mpr hxp)]
      · simp only [F,indicator_of_notMem hxp,indicator_of_notMem (fun h => hxp (hq.mp h))])
  simpa only [F,lintegral_indicator_const (hT _),one_mul] using H

/-- A useful geometric version: a continuous distance-to-segment function
and null distance spheres give continuous tube volume. -/
theorem continuous_volume_strict_sublevel
    {P X : Type*} [TopologicalSpace P] [FirstCountableTopology P] [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (d : P → X → ℝ) (r : ℝ)
    (hd : ∀ x,Continuous (fun p => d p x))
    (hm : ∀ p,Measurable (d p))
    (hz : ∀ p,μ {x | d p x=r}=0) :
    Continuous (fun p => μ {x | d p x<r}) := by
  apply continuous_volume_of_ae_stable_membership μ (fun p => {x | d p x<r})
    (fun p => measurableSet_lt (hm p) measurable_const)
  intro p
  have hne : ∀ᵐ x ∂μ,d p x≠r := by
    apply ae_iff.mpr
    simpa only [not_not] using hz p
  filter_upwards [hne] with x hx
  rcases lt_or_gt_of_ne hx with hlt | hgt
  · have H : ∀ᶠ q in 𝓝 p,d q x<r := (hd x).continuousAt.eventually (gt_mem_nhds hlt)
    filter_upwards [H] with q hq
    simp only [hlt, hq]
  · have H : ∀ᶠ q in 𝓝 p,r<d q x := (hd x).continuousAt.eventually (lt_mem_nhds hgt)
    filter_upwards [H] with q hq
    simp only [not_lt.mpr hgt.le,not_lt.mpr hq.le]

end OAI.Geometry.Nikodym
