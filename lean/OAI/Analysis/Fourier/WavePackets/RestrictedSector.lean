import OAI.Analysis.Fourier.WavePackets.SectorAssembly

namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory
open scoped ENNReal FourierTransform ContDiff

noncomputable local instance restrictedCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance restrictedCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance restrictedCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem ennreal_le_root_mul_of_rpow_le {A R B : ℝ≥0∞} {p : ℝ} (hp : 0 < p)
    (h : A ^ p ≤ R * B ^ p) : A ≤ R ^ (1 / p) * B := by
  have hh := ENNReal.rpow_le_rpow h (le_of_lt (one_div_pos.mpr hp))
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt (one_div_pos.mpr hp)),
    ← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one] using hh

/-- The restricted sector estimate is used only on the individual frequency
projections of amplitude pieces. The mixed L∞/L² input is bounded by the
genuine Lᵖ input, with the cutoff's proved L¹ kernel constant. -/
theorem restricted_sector_amplitude_bounds {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℂ} (hs : HasCompactSupport φ)
    (hφ : ContDiff ℝ ∞ φ) (hz : (0 : EuclideanSpace ℝ (Fin n)) ∉ tsupport φ)
    {h : ℝ} (hh : 0 < h) {f : UnitAddTorus (Fin n) → ℂ} (hf : Measurable f)
    {p : ℝ} (hp : 2 ≤ p) {R : ℝ≥0∞}
    {μ : Measure (ℝ × UnitAddTorus (Fin n))}
    (hr : ∀ g : UnitAddTorus (Fin n) → ℂ, Measurable g → Integrable g →
      (eLpNorm (fun q : ℝ × UnitAddTorus (Fin n) => periodicHalfWave φ h q.1 g q.2)
        (.ofReal p) μ) ^ p ≤
      R * ((eLpNorm (periodicHalfWave φ h 0 g) ⊤ volume) ^ (p - 2) *
        (eLpNorm (periodicHalfWave φ h 0 g) 2 volume) ^ (2 : ℝ))) :
    let D := (R * (eLpNorm (𝓕⁻ φ) 1 volume) ^ p * (2 : ℝ≥0∞) ^ (p - 2)) ^ (1 / p) *
      max 1 (eLpNorm f (.ofReal p) volume)
    eLpNorm (fun q : ℝ × UnitAddTorus (Fin n) =>
      periodicHalfWave φ h q.1 (amplitudeTruncation 1 f) q.2) (.ofReal p) μ ≤ D ∧
    ∀ j, eLpNorm (fun q : ℝ × UnitAddTorus (Fin n) =>
      periodicHalfWave φ h q.1 (amplitudePiece j f) q.2) (.ofReal p) μ ≤ D := by
  dsimp only
  have hp0 : 0 < p := by linarith
  have h2 : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ (p - 2) := by
    simpa only [ENNReal.one_rpow] using ENNReal.rpow_le_rpow
      (show (1 : ℝ≥0∞) ≤ 2 by norm_num) (show 0 ≤ p - 2 by linarith)
  constructor
  · have hl := (hr _ (measurable_amplitudeTruncation hf 1)
      (integrable_amplitudeTruncation_one hf)).trans
      (mul_le_mul' le_rfl (projected_lowAmplitude_mixed_norm_le hs hφ hz hh hf hp))
    have hl' : (eLpNorm (fun q : ℝ × UnitAddTorus (Fin n) =>
        periodicHalfWave φ h q.1 (amplitudeTruncation 1 f) q.2) (.ofReal p) μ) ^ p ≤
        (R * (eLpNorm (𝓕⁻ φ) 1 volume) ^ p * (2 : ℝ≥0∞) ^ (p - 2)) * 1 ^ p := by
      simpa only [ENNReal.one_rpow, mul_one] using hl.trans
        (show R * (eLpNorm (𝓕⁻ φ) 1 volume) ^ p ≤
            R * (eLpNorm (𝓕⁻ φ) 1 volume) ^ p * (2 : ℝ≥0∞) ^ (p - 2) from
          le_mul_of_one_le_right' h2)
    exact (ennreal_le_root_mul_of_rpow_le hp0 hl').trans
      (mul_le_mul' le_rfl (le_max_left _ _))
  · intro j
    have hj := (hr _ (measurable_amplitudePiece hf j) (integrable_amplitudePiece hf j)).trans
      (mul_le_mul' le_rfl (projected_amplitudePiece_mixed_norm_le hs hφ hz hh hf j hp))
    have hj' : (eLpNorm (fun q : ℝ × UnitAddTorus (Fin n) =>
        periodicHalfWave φ h q.1 (amplitudePiece j f) q.2) (.ofReal p) μ) ^ p ≤
        (R * (eLpNorm (𝓕⁻ φ) 1 volume) ^ p * (2 : ℝ≥0∞) ^ (p - 2)) *
          (eLpNorm f (.ofReal p) volume) ^ p := by
      simpa only [mul_assoc] using hj
    exact (ennreal_le_root_mul_of_rpow_le hp0 hj').trans
      (mul_le_mul' le_rfl (le_max_right _ _))

/-- The manuscript's restricted-type sector estimate assembles into an
ordinary Lᵖ estimate for bounded data. The only analytic premise here is
the displayed mixed-norm estimate for individual narrow sectors. -/
theorem periodic_bound_of_restricted_sectors {n : ℕ} {ι : Type*} (s : Finset ι)
    (φ : ι → EuclideanSpace ℝ (Fin n) → ℂ)
    (hs : ∀ i ∈ s, HasCompactSupport (φ i))
    (hφ : ∀ i ∈ s, ContDiff ℝ ∞ (φ i))
    (hz : ∀ i ∈ s, (0 : EuclideanSpace ℝ (Fin n)) ∉ tsupport (φ i))
    {h : ℝ} (hh : 0 < h) {f : UnitAddTorus (Fin n) → ℂ} (hf : Measurable f)
    (N : ℕ) (hN : ∀ x, ‖f x‖ < (2 : ℝ) ^ N)
    {p : ℝ} (hp : 2 ≤ p) {R K : ℝ≥0∞}
    {μ : Measure (ℝ × UnitAddTorus (Fin n))}
    (hK : ∀ i ∈ s, eLpNorm (𝓕⁻ (φ i)) 1 volume ≤ K)
    (hr : ∀ i ∈ s, ∀ g : UnitAddTorus (Fin n) → ℂ, Measurable g → Integrable g →
      (eLpNorm (fun q : ℝ × UnitAddTorus (Fin n) => periodicHalfWave (φ i) h q.1 g q.2)
        (.ofReal p) μ) ^ p ≤
      R * ((eLpNorm (periodicHalfWave (φ i) h 0 g) ⊤ volume) ^ (p - 2) *
        (eLpNorm (periodicHalfWave (φ i) h 0 g) 2 volume) ^ (2 : ℝ))) :
    eLpNorm (fun q : ℝ × UnitAddTorus (Fin n) =>
      periodicHalfWave (∑ i ∈ s, φ i) h q.1 f q.2) (.ofReal p) μ ≤
      (s.card : ℝ≥0∞) * (N + 1 : ℝ≥0∞) *
        ((R * K ^ p * (2 : ℝ≥0∞) ^ (p - 2)) ^ (1 / p) *
          max 1 (eLpNorm f (.ofReal p) volume)) := by
  have hp0 : 0 < p := by linarith
  have hpc : (1 : ℝ≥0∞) ≤ .ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith)
  have hm (i : ι) (hi : i ∈ s) :
      (R * (eLpNorm (𝓕⁻ (φ i)) 1 volume) ^ p * (2 : ℝ≥0∞) ^ (p - 2)) ^ (1 / p) *
          max 1 (eLpNorm f (.ofReal p) volume) ≤
      (R * K ^ p * (2 : ℝ≥0∞) ^ (p - 2)) ^ (1 / p) *
          max 1 (eLpNorm f (.ofReal p) volume) := by
    exact mul_le_mul' (ENNReal.rpow_le_rpow
      (mul_le_mul' (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (hK i hi) hp0.le)) le_rfl)
      (one_div_nonneg.mpr hp0.le)) le_rfl
  apply periodic_sector_amplitude_norm_bound s φ hs hh hf N hN hpc
  · intro i hi
    exact (restricted_sector_amplitude_bounds (hs i hi) (hφ i hi) (hz i hi) hh hf hp
      (hr i hi)).1.trans (hm i hi)
  · intro i hi j _
    exact ((restricted_sector_amplitude_bounds (hs i hi) (hφ i hi) (hz i hi) hh hf hp
      (hr i hi)).2 j).trans (hm i hi)

end OAI.Analysis.Fourier.WavePackets
