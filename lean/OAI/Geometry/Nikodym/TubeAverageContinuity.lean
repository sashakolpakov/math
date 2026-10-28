import OAI.Geometry.Nikodym.TubeVolumeContinuity
import OAI.Geometry.Nikodym.CompactMaximal

open _root_.MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace OAI.Geometry.Nikodym

theorem continuous_tube_integral_of_ae_stable_membership
    {P X : Type*} [TopologicalSpace P] [FirstCountableTopology P] [MeasurableSpace X]
    (μ : Measure X) (T : P → Set X) (hT : ∀ p,MeasurableSet (T p))
    (hstable : ∀ p,∀ᵐ x ∂μ,∀ᶠ q in 𝓝 p,(x∈T q ↔ x∈T p))
    (H : X → ℝ≥0∞) (hH : Measurable H) (hfin : ∫⁻ x,H x ∂μ < ⊤) :
    Continuous (fun p => ∫⁻ x in T p,H x ∂μ) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let F : P → X → ℝ≥0∞ := fun q => (T q).indicator H
  have hh := tendsto_lintegral_filter_of_dominated_convergence
    (μ := μ) (l := 𝓝 p) (F := F) (f := F p) H
    (Eventually.of_forall fun q => hH.indicator (hT q))
    (Eventually.of_forall fun q => Eventually.of_forall fun x => by
      by_cases hx : x∈T q <;> simp [F,hx]) hfin.ne
    ((hstable p).mono fun x hx => by
      apply tendsto_const_nhds.congr'
      filter_upwards [hx] with q hq
      by_cases hxp : x∈T p
      · simp only [F,indicator_of_mem hxp,indicator_of_mem (hq.mpr hxp)]
      · simp only [F,indicator_of_notMem hxp,indicator_of_notMem (fun h => hxp (hq.mp h))])
  exact show Tendsto _ (𝓝 p) (𝓝 _) from by
    simpa only [F,lintegral_indicator (hT _)] using hh

theorem continuous_tube_average_of_ae_stable_membership
    {P X : Type*} [TopologicalSpace P] [FirstCountableTopology P] [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (T : P → Set X) (hT : ∀ p,MeasurableSet (T p))
    (hstable : ∀ p,∀ᵐ x ∂μ,∀ᶠ q in 𝓝 p,(x∈T q ↔ x∈T p))
    (hpos : ∀ p,μ (T p) ≠ 0)
    (H : X → ℝ≥0∞) (hH : Measurable H) (hfin : ∫⁻ x,H x ∂μ < ⊤) :
    Continuous (fun p => (∫⁻ x in T p,H x ∂μ) / μ (T p)) := by
  have hn := continuous_tube_integral_of_ae_stable_membership μ T hT hstable H hH hfin
  have hd := continuous_volume_of_ae_stable_membership μ T hT hstable
  apply continuous_iff_continuousAt.mpr
  intro p
  exact ENNReal.Tendsto.div hn.continuousAt (Or.inr (hpos p)) hd.continuousAt
    (Or.inl (measure_ne_top μ _))

/-- A concrete compact endpoint-family criterion. Closed incidence and
admissibility are allowed; null tube boundaries provide continuity of the
actual normalized integrals, so no measurable-majorant replacement is used. -/
theorem measurable_compact_tube_maximal
    {P I X : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    [MeasurableSpace P] [BorelSpace P]
    [TopologicalSpace I] [FirstCountableTopology I] [CompactSpace I] [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (T : P × I → Set X)
    (hT : ∀ p,MeasurableSet (T p))
    (hstable : ∀ p,∀ᵐ x ∂μ,∀ᶠ q in 𝓝 p,(x∈T q ↔ x∈T p))
    (hpos : ∀ p,μ (T p) ≠ 0)
    (A : Set (P × I)) (hA : IsClosed A)
    (H : X → ℝ≥0∞) (hH : Measurable H) (hfin : ∫⁻ x,H x ∂μ < ⊤) :
    Measurable (fun p => ⨆ i,⨆ (_ : (p,i)∈A),
      (∫⁻ x in T (p,i),H x ∂μ) / μ (T (p,i))) :=
  measurable_compact_admissible_sup A hA _
    (continuous_tube_average_of_ae_stable_membership μ T hT hstable hpos H hH hfin)

end OAI.Geometry.Nikodym
