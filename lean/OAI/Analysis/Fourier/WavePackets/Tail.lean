import OAI.Analysis.Fourier.WavePackets.Uniform

namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory
open scoped RealInnerProductSpace ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [Measure.IsAddHaarMeasure μ]

omit [FiniteDimensional ℝ E] in
/-- Continuity of the actual oscillatory kernel, by dominated convergence in
the compactly supported frequency variable. -/
theorem continuous_semiclassicalWaveKernel {a : E → ℂ}
    (ha : Continuous a) (hs : HasCompactSupport a) (h T : ℝ) :
    Continuous (semiclassicalWaveKernel μ a h T) := by
  apply continuous_const.mul
  apply continuous_of_dominated
    (bound := fun ξ => ‖a ξ‖)
  · intro X
    apply Continuous.aestronglyMeasurable
    exact (continuous_oscillation (by unfold euclideanWavePhase; fun_prop) h).mul ha
  · intro X
    exact Filter.Eventually.of_forall fun ξ => by simp [norm_oscillation]
  · exact (ha.integrable_of_hasCompactSupport hs).norm
  · apply Filter.Eventually.of_forall
    intro ξ
    unfold oscillation euclideanWavePhase
    fun_prop

/-- The kernel restricted to the region separated from the wave cone. -/
noncomputable def waveTail (μ : Measure E) (a : E → ℂ) (h T : ℝ) : E → ℂ :=
  {X : E | 3 ≤ ‖X‖}.indicator (semiclassicalWaveKernel μ a h T)

omit [FiniteDimensional ℝ E] in
theorem stronglyMeasurable_waveTail {a : E → ℂ}
    (ha : Continuous a) (hs : HasCompactSupport a) (h T : ℝ) :
    StronglyMeasurable (waveTail μ a h T) := by
  apply (continuous_semiclassicalWaveKernel ha hs h T).stronglyMeasurable.indicator
  exact measurableSet_le measurable_const measurable_norm

/-- Spatially integrable polynomial majorant for the tail. Both its constant
and its spatial weight are independent of time and semiclassical scale. -/
theorem waveTail_uniform_majorant {a : E → ℂ}
    (ha : ContDiff ℝ ∞ a) (hzero : (0 : E) ∉ tsupport a)
    (hs : HasCompactSupport a) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T h : ℝ), 0 ≤ T → T ≤ 2 → 0 < h → h ≤ 1 →
      ∀ X, ‖waveTail μ a h T X‖ ≤
        C * h ^ N * (1 + ‖X‖) ^ (-(Module.finrank ℝ E + 1 : ℝ)) := by
  let d := Module.finrank ℝ E + 1
  obtain ⟨C, hC, hb⟩ := semiclassicalWaveKernel_off_cone (μ := μ) ha hzero hs (N + d)
  refine ⟨C, hC, ?_⟩
  intro T h hT₀ hT₁ hh hh₁ X
  by_cases hX : 3 ≤ ‖X‖
  · rw [waveTail, Set.indicator_of_mem (show X ∈ {X : E | 3 ≤ ‖X‖} from hX)]
    have hw : 1 ≤ 1 + ‖X‖ := by linarith [norm_nonneg X]
    have hp : h ^ (N + d) ≤ h ^ N := by
      rw [pow_add]
      exact mul_le_of_le_one_right (pow_nonneg hh.le N) (pow_le_one₀ hh.le hh₁)
    have hwp : (1 + ‖X‖) ^ d ≤ (1 + ‖X‖) ^ (N + d) :=
      pow_le_pow_right₀ hw (Nat.le_add_left d N)
    calc
      _ ≤ C * h ^ (N + d) / (1 + ‖X‖) ^ (N + d) := hb X T h hX hT₀ hT₁ hh
      _ ≤ C * h ^ N / (1 + ‖X‖) ^ d := by
        apply div_le_div₀ (mul_nonneg hC (pow_nonneg hh.le _))
          (mul_le_mul_of_nonneg_left hp hC) (by positivity) hwp
      _ = _ := by
        rw [Real.rpow_neg (by positivity), ← Nat.cast_one, ← Nat.cast_add,
          Real.rpow_natCast]
        rfl
  · simp only [waveTail, Set.indicator_of_notMem (show X ∉ {X : E | 3 ≤ ‖X‖} from hX), norm_zero]
    positivity

/-- Uniform `O(h^N)` L¹ norm of the genuine spatial kernel tail. -/
theorem waveTail_integrable_and_L1_bound {a : E → ℂ}
    (ha : ContDiff ℝ ∞ a) (hzero : (0 : E) ∉ tsupport a)
    (hs : HasCompactSupport a) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T h : ℝ), 0 ≤ T → T ≤ 2 → 0 < h → h ≤ 1 →
      Integrable (waveTail μ a h T) μ ∧
      (∫ X, ‖waveTail μ a h T X‖ ∂μ) ≤ C * h ^ N := by
  let w : E → ℝ := fun X => (1 + ‖X‖) ^ (-(Module.finrank ℝ E + 1 : ℝ))
  have hi : Integrable w μ := integrable_one_add_norm (by linarith)
  obtain ⟨C, hC, hb⟩ := waveTail_uniform_majorant (μ := μ) ha hzero hs N
  refine ⟨C * ∫ X, w X ∂μ, mul_nonneg hC (integral_nonneg fun X => by positivity), ?_⟩
  intro T h hT₀ hT₁ hh hh₁
  have hbound := hb T h hT₀ hT₁ hh hh₁
  have hint : Integrable (waveTail μ a h T) μ :=
    (hi.const_mul (C * h ^ N)).mono'
      (stronglyMeasurable_waveTail ha.continuous hs h T).aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  refine ⟨hint, ?_⟩
  calc
    _ ≤ ∫ X, C * h ^ N * w X ∂μ := integral_mono hint.norm (hi.const_mul _) hbound
    _ = _ := by rw [integral_const_mul]; ring

end OAI.Analysis.Fourier.WavePackets
