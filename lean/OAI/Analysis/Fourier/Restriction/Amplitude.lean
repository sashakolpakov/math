import OAI.Analysis.Fourier.Restriction.Truncation

open _root_.MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

def amplitudeBand {X : Type*} (f : X → ℂ) (l u : ℝ) : X → ℂ :=
  {x | l < ‖f x‖ ∧ ‖f x‖ ≤ u}.indicator f

theorem amplitudeBand_eq_high_sub_high {X : Type*} (f : X → ℂ)
    {l u : ℝ} (hlu : l ≤ u) (x : X) :
    amplitudeBand f l u x = amplitudeHigh f l x - amplitudeHigh f u x := by
  by_cases hl : l < ‖f x‖
  · by_cases hu : ‖f x‖ ≤ u
    · simp [amplitudeBand, amplitudeHigh, hl, hu, not_lt.mpr hu]
    · simp [amplitudeBand, amplitudeHigh, hl, hu, lt_of_not_ge hu]
  · have hu : ¬ u < ‖f x‖ := fun hu ↦ hl (hlu.trans_lt hu)
    simp [amplitudeBand, amplitudeHigh, hl, hu]

theorem measurable_amplitudeBand {X : Type*} [MeasurableSpace X]
    {f : X → ℂ} (hf : Measurable f) (l u : ℝ) :
    Measurable (amplitudeBand f l u) :=
  hf.indicator ((measurableSet_lt measurable_const hf.norm).inter
    (measurableSet_le hf.norm measurable_const))

theorem integrable_amplitudeBand {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℂ} (hf : Measurable f) (hfi : Integrable f μ) (l u : ℝ) :
    Integrable (amplitudeBand f l u) μ :=
  hfi.indicator ((measurableSet_lt measurable_const hf.norm).inter
    (measurableSet_le hf.norm measurable_const))

theorem norm_amplitudeBand_le {X : Type*} (f : X → ℂ) (l u : ℝ) (x : X) :
    ‖amplitudeBand f l u x‖ ≤ ‖f x‖ := by
  by_cases hx : l < ‖f x‖ ∧ ‖f x‖ ≤ u <;> simp [amplitudeBand, hx]

theorem norm_amplitudeBand_le_upper {X : Type*} (f : X → ℂ) (l : ℝ)
    {u : ℝ} (hu : 0 ≤ u) (x : X) : ‖amplitudeBand f l u x‖ ≤ u := by
  by_cases hx : l < ‖f x‖ ∧ ‖f x‖ ≤ u
  · simp [amplitudeBand, hx]
  · simp [amplitudeBand, hx, hu]

theorem amplitudeBand_eq_zero_of_le {X : Type*} (f : X → ℂ) (l u : ℝ)
    {x : X} (hx : ‖f x‖ ≤ l) : amplitudeBand f l u x = 0 := by
  simp [amplitudeBand, not_lt.mpr hx]

theorem sum_amplitudeBand_high {X : Type*} (f : X → ℂ) (a : ℕ → ℝ)
    (ha : Monotone a) (N : ℕ) (x : X) :
    (∑ k ∈ Finset.range N, amplitudeBand f (a k) (a (k + 1)) x) =
      amplitudeHigh f (a 0) x - amplitudeHigh f (a N) x := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, amplitudeBand_eq_high_sub_high f (ha (Nat.le_succ N))]
    ring

theorem sum_amplitudeBand_low {X : Type*} (f : X → ℂ) (a : ℕ → ℝ)
    (ha : Antitone a) (N : ℕ) (x : X) :
    (∑ k ∈ Finset.range N, amplitudeBand f (a (k + 1)) (a k) x) =
      amplitudeHigh f (a N) x - amplitudeHigh f (a 0) x := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, amplitudeBand_eq_high_sub_high f (ha (Nat.le_succ N))]
    ring

theorem tendsto_amplitudeBand {X : Type*} (f : X → ℂ) (x : X) :
    Tendsto (fun N : ℕ ↦ amplitudeBand f ((1 / 2 : ℝ) ^ N) ((2 : ℝ) ^ N) x)
      atTop (𝓝 (f x)) := by
  by_cases hz : f x = 0
  · have he : (fun N : ℕ ↦ amplitudeBand f ((1 / 2 : ℝ) ^ N) ((2 : ℝ) ^ N) x) =
        (fun _ ↦ 0) := by
      funext N
      simp [amplitudeBand, hz]
    rw [he, hz]
    exact tendsto_const_nhds
  · have hn : 0 < ‖f x‖ := norm_pos_iff.mpr hz
    have hlo : ∀ᶠ N : ℕ in atTop, (1 / 2 : ℝ) ^ N < ‖f x‖ :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).eventually (gt_mem_nhds hn)
    have hhi : ∀ᶠ N : ℕ in atTop, ‖f x‖ ≤ (2 : ℝ) ^ N :=
      (tendsto_atTop.1 (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))) ‖f x‖
    apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [hlo, hhi] with N hN hN'
    exact (Set.indicator_of_mem (show x ∈ {y | (1 / 2 : ℝ) ^ N < ‖f y‖ ∧
      ‖f y‖ ≤ (2 : ℝ) ^ N} from ⟨hN, hN'⟩) f).symm

end OAI.Analysis.Fourier.Restriction
