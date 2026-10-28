import OAI.MeasureTheory.Kakeya.Volume

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section
namespace OAI.MeasureTheory.Kakeya

/-- Fatou's lemma gives lower semicontinuity after integration in any
first-countable parameter space. -/
theorem lowerSemicontinuous_lintegral_family
    {P α : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    [MeasurableSpace α] {μ : Measure α} (F : P → α → ℝ≥0∞)
    (hm : ∀ p, AEMeasurable (F p) μ) (hl : ∀ a, LowerSemicontinuous (fun p ↦ F p a)) :
    LowerSemicontinuous (fun p ↦ ∫⁻ a, F p a ∂μ) := by
  apply lowerSemicontinuous_iff_le_liminf.mpr
  intro p
  calc
    (∫⁻ a, F p a ∂μ) ≤ ∫⁻ a, liminf (fun p ↦ F p a) (𝓝 p) ∂μ :=
      lintegral_mono fun a ↦ (hl a).le_liminf p
    _ ≤ liminf (fun p ↦ ∫⁻ a, F p a ∂μ) (𝓝 p) := lintegral_liminf_le' hm

theorem isOpen_tube_parameter_set {n : ℕ} (δ : ℝ) (y : Space n) :
    IsOpen {z : Space n × Space n | y ∈ OAI.MeasureTheory.Kakeya.tube δ z.1 z.2} := by
  have heq : {z : Space n × Space n | y ∈ OAI.MeasureTheory.Kakeya.tube δ z.1 z.2} =
      ⋃ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2),
        {z : Space n × Space n | dist y (z.2 + t • z.1) < δ} := by
    ext z
    simp only [Set.mem_ofPred_eq, OAI.MeasureTheory.Kakeya.tube, Set.mem_iUnion, Metric.mem_ball]
  rw [heq]
  apply isOpen_iUnion
  intro t
  apply isOpen_iUnion
  intro _
  exact isOpen_lt (by fun_prop) continuous_const

def tubeMass {n : ℕ} (δ : ℝ) (f : Space n → ℂ) (v x : Space n) : ℝ≥0∞ :=
  ∫⁻ y in OAI.MeasureTheory.Kakeya.tube δ v x, ‖f y‖ₑ

theorem lowerSemicontinuous_tubeMass {n : ℕ} (δ : ℝ) (f : Space n → ℂ)
    (hf : AEStronglyMeasurable f (volume : Measure (Space n))) :
    LowerSemicontinuous (fun z : Space n × Space n ↦ tubeMass δ f z.1 z.2) := by
  let F : (Space n × Space n) → Space n → ℝ≥0∞ :=
    fun z y ↦ (OAI.MeasureTheory.Kakeya.tube δ z.1 z.2).indicator (fun y ↦ ‖f y‖ₑ) y
  have hm (z : Space n × Space n) : AEMeasurable (F z) (volume : Measure (Space n)) :=
    hf.enorm.indicator (measurableSet_tube _ _ _)
  have hl (y : Space n) : LowerSemicontinuous (fun z ↦ F z y) := by
    change LowerSemicontinuous
      ({z : Space n × Space n | y ∈ OAI.MeasureTheory.Kakeya.tube δ z.1 z.2}.indicator (fun _ ↦ ‖f y‖ₑ))
    exact (isOpen_tube_parameter_set δ y).lowerSemicontinuous_indicator bot_le
  have h := lowerSemicontinuous_lintegral_family F hm hl
  convert h using 1
  funext z
  exact (lintegral_indicator (measurableSet_tube _ _ _) _).symm

theorem lowerSemicontinuous_iSup_slices {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    (F : P × X → ℝ≥0∞) (hF : LowerSemicontinuous F) :
    LowerSemicontinuous (fun p ↦ ⨆ x : X, F (p, x)) := by
  have hs (x : X) : LowerSemicontinuous (fun p : P ↦ F (p, x)) :=
    hF.comp (continuous_id.prodMk continuous_const)
  exact lowerSemicontinuous_iSup hs

theorem lowerSemicontinuous_sup_tubeMass {n : ℕ} (δ : ℝ) (f : Space n → ℂ)
    (hf : AEStronglyMeasurable f (volume : Measure (Space n))) :
    LowerSemicontinuous (fun v ↦ ⨆ x : Space n, tubeMass δ f v x) := by
  exact lowerSemicontinuous_iSup_slices (fun z : Space n × Space n ↦ tubeMass δ f z.1 z.2)
    (lowerSemicontinuous_tubeMass δ f hf)

theorem lowerSemicontinuous_volume_tube {n : ℕ} (δ : ℝ) :
    LowerSemicontinuous (fun v : Space n ↦ volume (OAI.MeasureTheory.Kakeya.tube δ v 0)) := by
  have h := (lowerSemicontinuous_tubeMass δ (fun _ : Space n ↦ (1 : ℂ))
    aestronglyMeasurable_const).comp
      (show Continuous (fun v : Space n ↦ (v, (0 : Space n))) by fun_prop)
  simpa [Function.comp_def, tubeMass] using h

/-- The genuine supremum over all tube centers is measurable. The numerator
is lower semicontinuous by Fatou, while the denominator is independent of the
center and is itself a measurable parameter integral. -/
theorem measurable_kakeyaMaximal {n : ℕ} (δ : ℝ) (f : Space n → ℂ)
    (hf : AEStronglyMeasurable f (volume : Measure (Space n))) :
    Measurable (OAI.MeasureTheory.Kakeya.kakeyaMaximal δ f) := by
  have heq : OAI.MeasureTheory.Kakeya.kakeyaMaximal δ f = fun v ↦
      (⨆ x : Space n, tubeMass δ f v x) / volume (OAI.MeasureTheory.Kakeya.tube δ v 0) := by
    funext v
    change (⨆ x : Space n, tubeMass δ f v x / volume (OAI.MeasureTheory.Kakeya.tube δ v x)) = _
    simp_rw [volume_tube_center_eq]
    exact (ENNReal.iSup_div _ _).symm
  rw [heq]
  exact (lowerSemicontinuous_sup_tubeMass δ f hf).measurable.div
    (lowerSemicontinuous_volume_tube δ).measurable

end OAI.MeasureTheory.Kakeya
