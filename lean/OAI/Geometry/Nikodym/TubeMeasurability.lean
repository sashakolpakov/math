import OAI.Geometry.Nikodym.MetricMaximal

open _root_.MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace OAI.Geometry.Nikodym


theorem lowerSemicontinuous_indicator_ennreal {P : Type*} [TopologicalSpace P]
    {S : Set P} (hS : IsOpen S) {f : P → ℝ≥0∞} (hf : LowerSemicontinuous f) :
    LowerSemicontinuous (S.indicator f) := by
  intro x z hz
  have hx : x∈S := by
    by_contra hn
    simp only [indicator_of_notMem hn,not_lt_zero] at hz
  have hz' : z<f x := by simpa only [indicator_of_mem hx] using hz
  filter_upwards [hS.mem_nhds hx,hf x z hz'] with y hy hzy
  simpa only [indicator_of_mem hy] using hzy

/-- A continuously varying family of tube volumes and open tube membership
give lower semicontinuous normalized averages, by Fatou applied after division.
The input need only be a.e. measurable. -/
theorem lowerSemicontinuous_tube_average
    {P X : Type*} [TopologicalSpace P] [FirstCountableTopology P] [MeasurableSpace X]
    (μ : Measure X) (T : P → Set X) (hT : ∀ p,MeasurableSet (T p))
    (hopen : ∀ x,IsOpen {p | x∈T p}) (hvol : Continuous (fun p => μ (T p)))
    (f : X → ℂ) (hf : AEStronglyMeasurable f μ) :
    LowerSemicontinuous (fun p => (∫⁻ x in T p,‖f x‖ₑ ∂μ)/μ (T p)) := by
  let F : P → X → ℝ≥0∞ := fun p x => (T p).indicator (fun x => ‖f x‖ₑ/μ (T p)) x
  have hFm (p : P) : AEMeasurable (F p) μ := (hf.enorm.div_const _).indicator (hT p)
  have hFl (x : X) : LowerSemicontinuous (fun p => F p x) := by
    change LowerSemicontinuous ({p | x∈T p}.indicator (fun p => ‖f x‖ₑ/μ (T p)))
    apply lowerSemicontinuous_indicator_ennreal (hopen x)
    apply Continuous.lowerSemicontinuous
    simpa only [div_eq_mul_inv,Function.comp_def] using
      (ENNReal.continuous_const_mul (by finiteness : ‖f x‖ₑ≠⊤)).comp
        (continuous_inv.comp hvol)
  have H := OAI.MeasureTheory.Kakeya.lowerSemicontinuous_lintegral_family F hFm hFl
  convert H using 1
  funext p
  rw [show (∫⁻ x,F p x ∂μ) = ∫⁻ x in T p,‖f x‖ₑ/μ (T p) ∂μ from
    lintegral_indicator (hT p) _]
  simp only [div_eq_mul_inv]
  rw [lintegral_mul_const'' _ hf.restrict.enorm]

/-- A supremum over an arbitrary, possibly uncountable direction family is
measurable when the geometric tubes have open membership, continuous volume,
and open admissibility. No countability of the direction set is asserted. -/
theorem measurable_admissible_tube_sup
    {P X ι : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    [MeasurableSpace P] [BorelSpace P] [MeasurableSpace X]
    (μ : Measure X) (T : P → ι → Set X) (admissible : P → ι → Prop)
    (hT : ∀ p i,MeasurableSet (T p i))
    (hopen : ∀ i x,IsOpen {p | x∈T p i})
    (hvol : ∀ i,Continuous (fun p => μ (T p i)))
    (hadm : ∀ i,IsOpen {p | admissible p i})
    (f : X → ℂ) (hf : AEStronglyMeasurable f μ) :
    Measurable (fun p => ⨆ i,⨆ (_ : admissible p i),
      (∫⁻ x in T p i,‖f x‖ₑ ∂μ)/μ (T p i)) := by
  apply LowerSemicontinuous.measurable
  apply lowerSemicontinuous_iSup
  intro i
  have H := lowerSemicontinuous_indicator_ennreal (hadm i)
    (lowerSemicontinuous_tube_average μ (fun p => T p i) (fun p => hT p i)
      (hopen i) (hvol i) f hf)
  convert H using 1
  funext p
  by_cases hp : admissible p i <;> simp [hp]

theorem isOpen_metricTube_membership {P X J : Type*} [TopologicalSpace P] [MetricSpace X]
    (γ : P → J → X) (hγ : ∀ t,Continuous (fun p => γ p t)) (δ : ℝ) (x : X) :
    IsOpen {p | x∈metricTube δ (range (γ p))} := by
  have he : {p | x∈metricTube δ (range (γ p))} =
      ⋃ t,{p | dist x (γ p t)<δ} := by
    ext p
    simp only [metricTube,mem_ofPred_eq,mem_range,mem_iUnion]
    constructor
    · rintro ⟨y,⟨t,rfl⟩,h⟩
      exact ⟨t,h⟩
    · rintro ⟨t,h⟩
      exact ⟨γ p t,⟨t,rfl⟩,h⟩
  rw [he]
  exact isOpen_iUnion fun t => isOpen_lt (continuous_const.dist (hγ t)) continuous_const

end OAI.Geometry.Nikodym
