import OAI.Analysis.Fourier.WavePackets.SectorMultiplier
import OAI.Analysis.Fourier.WavePackets.Cubes

namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory
open scoped ENNReal FourierTransform ContDiff

noncomputable def amplitudeTruncation {X : Type*} (a : ℝ) (f : X → ℂ) : X → ℂ :=
  {x | ‖f x‖ < a}.indicator f

noncomputable def amplitudePiece {X : Type*} (j : ℕ) (f : X → ℂ) : X → ℂ :=
  {x | (2 : ℝ) ^ j ≤ ‖f x‖ ∧ ‖f x‖ < (2 : ℝ) ^ (j + 1)}.indicator f

theorem measurable_amplitudeTruncation {X : Type*} [MeasurableSpace X]
    {f : X → ℂ} (hf : Measurable f) (a : ℝ) : Measurable (amplitudeTruncation a f) :=
  hf.indicator (measurableSet_lt hf.norm measurable_const)

theorem measurable_amplitudePiece {X : Type*} [MeasurableSpace X]
    {f : X → ℂ} (hf : Measurable f) (j : ℕ) : Measurable (amplitudePiece j f) :=
  hf.indicator ((measurableSet_le measurable_const hf.norm).inter
    (measurableSet_lt hf.norm measurable_const))

theorem amplitudeTruncation_succ {X : Type*} (f : X → ℂ) (j : ℕ) :
    amplitudeTruncation ((2 : ℝ) ^ (j + 1)) f =
      amplitudeTruncation ((2 : ℝ) ^ j) f + amplitudePiece j f := by
  funext x
  have hpow : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ (j + 1) := by
    rw [pow_succ]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) j]
  by_cases h₀ : ‖f x‖ < (2 : ℝ) ^ j
  · have h₁ := lt_of_lt_of_le h₀ hpow
    simp [amplitudeTruncation, amplitudePiece, h₀, h₁, not_le.mpr h₀]
  · by_cases h₁ : ‖f x‖ < (2 : ℝ) ^ (j + 1)
    · simp [amplitudeTruncation, amplitudePiece, h₀, h₁, le_of_not_gt h₀]
    · simp [amplitudeTruncation, amplitudePiece, h₀, h₁]

/-- A bounded function decomposes exactly into the low-amplitude piece
and finitely many dyadic shells; the pieces need not be frequency localized. -/
theorem amplitude_decomposition {X : Type*} (f : X → ℂ) (N : ℕ)
    (hN : ∀ x, ‖f x‖ < (2 : ℝ) ^ N) :
    f = amplitudeTruncation 1 f + ∑ j ∈ Finset.range N, amplitudePiece j f := by
  have hsum : amplitudeTruncation ((2 : ℝ) ^ N) f =
      amplitudeTruncation 1 f + ∑ j ∈ Finset.range N, amplitudePiece j f := by
    clear hN
    induction N with
    | zero => simp
    | succ N ih => rw [amplitudeTruncation_succ, ih, Finset.sum_range_succ, add_assoc]
  rw [← hsum]
  funext x
  simp [amplitudeTruncation, hN x]

/-- Exponential-in-`L` amplitude growth costs only `O(L)` dyadic shells.
This is the quantitative counting step for the smoothed annular input. -/
theorem amplitude_decomposition_logarithmic_count {X : Type*} (f : X → ℂ)
    {a L : ℝ} (ha : 0 ≤ a) (hL : 1 ≤ L) (hf : ∀ x, ‖f x‖ ≤ Real.exp (a * L)) :
    ∃ N : ℕ, (N : ℝ) ≤ (a / Real.log 2 + 2) * L ∧
      f = amplitudeTruncation 1 f + ∑ j ∈ Finset.range N, amplitudePiece j f := by
  let N : ℕ := ⌈a * L / Real.log 2⌉₊ + 1
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : 0 ≤ a * L / Real.log 2 := by positivity
  have hceil := Nat.ceil_lt_add_one hq
  have hlower := Nat.le_ceil (a * L / Real.log 2)
  have hNlower : a * L < (N : ℝ) * Real.log 2 := by
    have hlt : a * L / Real.log 2 < (N : ℝ) := by dsimp [N]; push_cast; linarith
    exact (div_lt_iff₀ hlog).mp hlt
  refine ⟨N, ?_, amplitude_decomposition f N (fun x => (hf x).trans_lt ?_)⟩
  · have hNupper : (N : ℝ) < a * L / Real.log 2 + 2 := by dsimp [N]; push_cast; linarith
    have heq : a * L / Real.log 2 + 2 * L = (a / Real.log 2 + 2) * L := by ring
    rw [← heq]
    linarith
  · calc
      Real.exp (a * L) < Real.exp ((N : ℝ) * Real.log 2) := Real.exp_lt_exp.mpr hNlower
      _ = (2 : ℝ) ^ N := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]

theorem amplitudeTruncation_one_enorm_le {X : Type*} (f : X → ℂ) (x : X) :
    ‖amplitudeTruncation 1 f x‖ₑ ≤ 1 := by
  by_cases hx : ‖f x‖ < 1
  · rw [amplitudeTruncation, Set.indicator_of_mem (show x ∈ {x | ‖f x‖ < 1} from hx),
      ← ofReal_norm, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hx.le
  · simp [amplitudeTruncation, hx]

theorem amplitudeTruncation_one_norm_le {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] {f : X → ℂ} (hf : Measurable f) (p : ℝ≥0∞) :
    eLpNorm (amplitudeTruncation 1 f) p μ ≤ 1 := by
  simpa using eLpNorm_le_of_ae_enorm_bound (μ := μ) (p := p)
    (measurable_amplitudeTruncation hf 1).aestronglyMeasurable
    (Filter.Eventually.of_forall (amplitudeTruncation_one_enorm_le f))

theorem amplitudePiece_enorm_le {X : Type*} (f : X → ℂ) (j : ℕ) (x : X) :
    ‖amplitudePiece j f x‖ₑ ≤ (2 : ℝ≥0∞) ^ (j + 1) := by
  by_cases hx : (2 : ℝ) ^ j ≤ ‖f x‖ ∧ ‖f x‖ < (2 : ℝ) ^ (j + 1)
  · rw [amplitudePiece, Set.indicator_of_mem (show x ∈
      {x | (2 : ℝ) ^ j ≤ ‖f x‖ ∧ ‖f x‖ < (2 : ℝ) ^ (j + 1)} from hx)]
    rw [← ofReal_norm, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_pow (by norm_num)]
    exact ENNReal.ofReal_le_ofReal hx.2.le
  · simp [amplitudePiece, hx]

/-- The shell's lower amplitude gives precisely the mixed-norm bound
needed for the sector estimate, with no finite-integral convention. -/
theorem amplitudePiece_mixed_integral_le {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℂ} (hf : Measurable f) (j : ℕ)
    {p : ℝ} (hp : 2 ≤ p) :
    ((2 : ℝ≥0∞) ^ j) ^ (p - 2) * (∫⁻ x, ‖amplitudePiece j f x‖ₑ ^ (2 : ℝ) ∂μ) ≤
      ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  rw [← lintegral_const_mul _ ((measurable_amplitudePiece hf j).enorm.pow_const _)]
  apply lintegral_mono
  intro x
  dsimp only
  by_cases hx : (2 : ℝ) ^ j ≤ ‖f x‖ ∧ ‖f x‖ < (2 : ℝ) ^ (j + 1)
  · rw [amplitudePiece, Set.indicator_of_mem (show x ∈
      {x | (2 : ℝ) ^ j ≤ ‖f x‖ ∧ ‖f x‖ < (2 : ℝ) ^ (j + 1)} from hx)]
    have ha : (2 : ℝ≥0∞) ^ j ≤ ‖f x‖ₑ := by
      rw [← ofReal_norm, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_pow (by norm_num)]
      exact ENNReal.ofReal_le_ofReal hx.1
    calc
      _ ≤ ‖f x‖ₑ ^ (p - 2) * ‖f x‖ₑ ^ (2 : ℝ) :=
        mul_le_mul' (ENNReal.rpow_le_rpow ha (by linarith)) le_rfl
      _ = ‖f x‖ₑ ^ p := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ (by linarith) (by norm_num)]
        congr 1
        ring
  · simp [amplitudePiece, hx]

theorem amplitudePiece_mixed_norm_le {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℂ} (hf : Measurable f) (j : ℕ)
    {p : ℝ} (hp : 2 ≤ p) :
    ((2 : ℝ≥0∞) ^ j) ^ (p - 2) * (eLpNorm (amplitudePiece j f) 2 μ) ^ (2 : ℝ) ≤
      (eLpNorm f (ENNReal.ofReal p) μ) ^ p := by
  have hp₀ : 0 < p := by linarith
  have htwo : (eLpNorm (amplitudePiece j f) 2 μ) ^ (2 : ℝ) =
      ∫⁻ x, ‖amplitudePiece j f x‖ₑ ^ (2 : ℝ) ∂μ := by
    simpa using eLpNorm_rpow_eq_lintegral (p := 2) (by norm_num) (by simp)
      (measurable_amplitudePiece hf j).aestronglyMeasurable
  have hpow : (eLpNorm f (ENNReal.ofReal p) μ) ^ p = ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
    simpa only [ENNReal.toReal_ofReal hp₀.le] using eLpNorm_rpow_eq_lintegral
      (ENNReal.ofReal_ne_zero_iff.mpr hp₀) ENNReal.ofReal_ne_top hf.aestronglyMeasurable
  rw [htwo, hpow]
  exact amplitudePiece_mixed_integral_le hf j hp

theorem integrable_amplitudePiece {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {f : X → ℂ} (hf : Measurable f) (j : ℕ) :
    Integrable (amplitudePiece j f) μ := by
  apply memLp_one_iff_integrable.mp
  apply lt_of_le_of_lt (eLpNorm_le_of_ae_enorm_bound (μ := μ) (p := 1)
    (measurable_amplitudePiece hf j).aestronglyMeasurable
    (Filter.Eventually.of_forall (amplitudePiece_enorm_le f j)))
  simp only [ENNReal.toReal_one, inv_one, ENNReal.rpow_one, smul_eq_mul]
  exact ENNReal.mul_lt_top (by finiteness) (measure_lt_top _ _)

theorem integrable_amplitudeTruncation_one {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {f : X → ℂ} (hf : Measurable f) :
    Integrable (amplitudeTruncation 1 f) μ := by
  apply memLp_one_iff_integrable.mp
  apply lt_of_le_of_lt (eLpNorm_le_of_ae_enorm_bound (μ := μ) (p := 1)
    (measurable_amplitudeTruncation hf 1).aestronglyMeasurable
    (Filter.Eventually.of_forall (amplitudeTruncation_one_enorm_le f)))
  simp

theorem mixed_product_bound {K X Y A : ℝ≥0∞} {p : ℝ} (hp : 2 ≤ p)
    (hY : Y ≤ K * (2 * A)) :
    Y ^ (p - 2) * (K * X) ^ (2 : ℝ) ≤
      K ^ p * (2 : ℝ≥0∞) ^ (p - 2) * (A ^ (p - 2) * X ^ (2 : ℝ)) := by
  calc
    _ ≤ (K * (2 * A)) ^ (p - 2) * (K * X) ^ (2 : ℝ) :=
      mul_le_mul' (ENNReal.rpow_le_rpow hY (by linarith)) le_rfl
    _ = (K ^ (p - 2) * K ^ (2 : ℝ)) *
        (2 ^ (p - 2) * (A ^ (p - 2) * X ^ (2 : ℝ))) := by
      simp only [ENNReal.mul_rpow_of_nonneg _ _ (by linarith : 0 ≤ p - 2),
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
      ac_rfl
    _ = _ := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by linarith) (by norm_num),
        sub_add_cancel]
      ac_rfl

section Periodic

noncomputable local instance amplitudeCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance amplitudeCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance amplitudeCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Applying the sector multiplier after amplitude truncation preserves
the exact mixed-norm control needed by the restricted sector theorem. -/
theorem projected_amplitudePiece_mixed_norm_le {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℂ} (hs : HasCompactSupport φ)
    (hφ : ContDiff ℝ ∞ φ) (hz : (0 : EuclideanSpace ℝ (Fin n)) ∉ tsupport φ)
    {h : ℝ} (hh : 0 < h) {f : UnitAddTorus (Fin n) → ℂ} (hf : Measurable f)
    (j : ℕ) {p : ℝ} (hp : 2 ≤ p) :
    (eLpNorm (periodicHalfWave φ h 0 (amplitudePiece j f)) ⊤ volume) ^ (p - 2) *
      (eLpNorm (periodicHalfWave φ h 0 (amplitudePiece j f)) 2 volume) ^ (2 : ℝ) ≤
    (eLpNorm (𝓕⁻ φ) 1 volume) ^ p * (2 : ℝ≥0∞) ^ (p - 2) *
      (eLpNorm f (ENNReal.ofReal p) volume) ^ p := by
  let K := eLpNorm (𝓕⁻ φ) 1 volume
  have hi := integrable_amplitudePiece (μ := volume) hf j
  have htwo := periodic_cutoff_norm_bound hs hφ hz hh
    (measurable_amplitudePiece hf j) hi (p := 2) (by norm_num) (by simp)
  have htop := periodic_cutoff_top_norm_bound hs hφ hz hh
    (measurable_amplitudePiece hf j) hi (amplitudePiece_enorm_le f j)
  have htop' : eLpNorm (periodicHalfWave φ h 0 (amplitudePiece j f)) ⊤ volume ≤
      K * (2 * (2 : ℝ≥0∞) ^ j) := by simpa [K, pow_succ, mul_comm] using htop
  calc
    _ ≤ (eLpNorm (periodicHalfWave φ h 0 (amplitudePiece j f)) ⊤ volume) ^ (p - 2) *
        (K * eLpNorm (amplitudePiece j f) 2 volume) ^ (2 : ℝ) :=
      mul_le_mul' le_rfl (ENNReal.rpow_le_rpow htwo (by norm_num))
    _ ≤ K ^ p * (2 : ℝ≥0∞) ^ (p - 2) *
        (((2 : ℝ≥0∞) ^ j) ^ (p - 2) * (eLpNorm (amplitudePiece j f) 2 volume) ^ (2 : ℝ)) :=
      mixed_product_bound hp htop'
    _ ≤ _ := mul_le_mul' le_rfl (amplitudePiece_mixed_norm_le hf j hp)

theorem projected_lowAmplitude_mixed_norm_le {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℂ} (hs : HasCompactSupport φ)
    (hφ : ContDiff ℝ ∞ φ) (hz : (0 : EuclideanSpace ℝ (Fin n)) ∉ tsupport φ)
    {h : ℝ} (hh : 0 < h) {f : UnitAddTorus (Fin n) → ℂ} (hf : Measurable f)
    {p : ℝ} (hp : 2 ≤ p) :
    (eLpNorm (periodicHalfWave φ h 0 (amplitudeTruncation 1 f)) ⊤ volume) ^ (p - 2) *
      (eLpNorm (periodicHalfWave φ h 0 (amplitudeTruncation 1 f)) 2 volume) ^ (2 : ℝ) ≤
      (eLpNorm (𝓕⁻ φ) 1 volume) ^ p := by
  let K := eLpNorm (𝓕⁻ φ) 1 volume
  have hi := integrable_amplitudeTruncation_one (μ := volume) hf
  have ht : eLpNorm (periodicHalfWave φ h 0 (amplitudeTruncation 1 f)) ⊤ volume ≤ K := by
    simpa only [mul_one] using periodic_cutoff_top_norm_bound hs hφ hz hh
      (measurable_amplitudeTruncation hf 1) hi (amplitudeTruncation_one_enorm_le f)
  have htwo : eLpNorm (periodicHalfWave φ h 0 (amplitudeTruncation 1 f)) 2 volume ≤ K := by
    have hb := periodic_cutoff_norm_bound hs hφ hz hh
      (measurable_amplitudeTruncation hf 1) hi (p := 2) (by norm_num) (by simp)
    calc
      _ ≤ K * eLpNorm (amplitudeTruncation 1 f) 2 volume := hb
      _ ≤ K * 1 := mul_le_mul' le_rfl (amplitudeTruncation_one_norm_le (μ := volume) hf 2)
      _ = K := mul_one K
  calc
    _ ≤ K ^ (p - 2) * K ^ (2 : ℝ) := mul_le_mul'
      (ENNReal.rpow_le_rpow ht (by linarith)) (ENNReal.rpow_le_rpow htwo (by norm_num))
    _ = _ := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by linarith) (by norm_num), sub_add_cancel]

end Periodic

end OAI.Analysis.Fourier.WavePackets
