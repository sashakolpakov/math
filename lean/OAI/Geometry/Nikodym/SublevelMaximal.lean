import OAI.Geometry.Nikodym.TubeAverageContinuity

open Set Filter _root_.MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace OAI.Geometry.Nikodym

theorem ae_stable_strict_sublevel
    {P X : Type*} [TopologicalSpace P] [MeasurableSpace X]
    (μ : Measure X) (d : P → X → ℝ) (r : ℝ)
    (hd : ∀ x,Continuous (fun p => d p x))
    (hz : ∀ p,μ {x | d p x=r}=0) :
    ∀ p,∀ᵐ x ∂μ,∀ᶠ q in 𝓝 p,(d q x<r ↔ d p x<r) := by
  intro p
  have hne : ∀ᵐ x ∂μ,d p x≠r := by
    apply ae_iff.mpr
    simpa only [not_not] using hz p
  filter_upwards [hne] with x hx
  rcases lt_or_gt_of_ne hx with hlt | hgt
  · have H : ∀ᶠ q in 𝓝 p,d q x<r := (hd x).continuousAt.eventually (gt_mem_nhds hlt)
    exact H.mono fun q hq => by simp only [hlt,hq]
  · have H : ∀ᶠ q in 𝓝 p,r<d q x := (hd x).continuousAt.eventually (lt_mem_nhds hgt)
    exact H.mono fun q hq => by simp only [not_lt.mpr hgt.le,not_lt.mpr hq.le]

/-- Null level sets give continuity of the actual normalized integral for
arbitrary almost-everywhere measurable integrable data. -/
theorem continuous_strict_sublevel_average
    {P X : Type*} [TopologicalSpace P] [FirstCountableTopology P] [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (d : P → X → ℝ) (r : ℝ)
    (hd : ∀ x,Continuous (fun p => d p x)) (hm : ∀ p,Measurable (d p))
    (hz : ∀ p,μ {x | d p x=r}=0) (hp : ∀ p,μ {x | d p x<r} ≠ 0)
    (H : X → ℝ≥0∞) (hH : AEMeasurable H μ) (hfin : ∫⁻ x,H x ∂μ < ⊤) :
    Continuous (fun p => (∫⁻ x in {x | d p x<r},H x ∂μ) / μ {x | d p x<r}) := by
  have he (p : P) : (∫⁻ x in {x | d p x<r},H x ∂μ) =
      ∫⁻ x in {x | d p x<r},hH.mk H x ∂μ :=
    lintegral_congr_ae (ae_restrict_of_ae hH.ae_eq_mk)
  have hf : (∫⁻ x,hH.mk H x ∂μ) < ⊤ := by
    rwa [← lintegral_congr_ae hH.ae_eq_mk]
  have hc := continuous_tube_average_of_ae_stable_membership μ
    (fun p => {x | d p x<r})
    (fun p => measurableSet_lt (hm p) measurable_const)
    (ae_stable_strict_sublevel μ d r hd hz) hp
    (hH.mk H) hH.measurable_mk hf
  simpa only [he] using hc

theorem measurable_compact_strict_sublevel_maximal
    {P I X : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    [MeasurableSpace P] [BorelSpace P]
    [TopologicalSpace I] [FirstCountableTopology I] [CompactSpace I] [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (d : P × I → X → ℝ) (r : ℝ)
    (hd : ∀ x,Continuous (fun p => d p x)) (hm : ∀ p,Measurable (d p))
    (hz : ∀ p,μ {x | d p x=r}=0) (hp : ∀ p,μ {x | d p x<r} ≠ 0)
    (A : Set (P × I)) (hA : IsClosed A)
    (H : X → ℝ≥0∞) (hH : AEMeasurable H μ) (hfin : ∫⁻ x,H x ∂μ < ⊤) :
    Measurable (fun p => ⨆ i,⨆ (_ : (p,i)∈A),
      (∫⁻ x in {x | d (p,i) x<r},H x ∂μ) / μ {x | d (p,i) x<r}) :=
  measurable_compact_admissible_sup A hA _
    (continuous_strict_sublevel_average μ d r hd hm hz hp H hH hfin)

end OAI.Geometry.Nikodym
