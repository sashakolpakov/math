import OAI.Analysis.Fourier.WavePackets.AmplitudeCount
import OAI.Analysis.Fourier.WavePackets.SectorMultiplier
import OAI.Analysis.PDE.Concentration.SectorCutoffs

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set _root_.MeasureTheory OAI.Analysis.PDE.Concentration
open scoped ENNReal FourierTransform ContDiff

local instance preprojectionCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance preprojectionCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance preprojectionCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem mFourierCoeff_periodic_cutoff {n : ℕ} {ψ : Space n → ℂ}
    (hc : HasCompactSupport ψ) {h : ℝ} (hh : 0 < h)
    (f : UnitAddTorus (Fin n) → ℂ) (k : Fin n → ℤ) :
    UnitAddTorus.mFourierCoeff (periodicHalfWave ψ h 0 f) k =
      ψ (h • periodicFrequency k) * UnitAddTorus.mFourierCoeff f k := by
  classical
  obtain ⟨s, hs, hoff⟩ := exists_spectral_index_set hc hh
  rw [periodicHalfWave_zero_eq_spectralTorusPolynomial s ψ h hoff]
  unfold spectralTorusPolynomial
  by_cases hk : k ∈ s
  · exact mFourierCoeff_torusIndexedWave_at (fun j : s => j.val)
      Subtype.val_injective _ ⟨k, hk⟩
  · rw [mFourierCoeff_torusIndexedWave_off]
    · simp [hoff k hk]
    · simpa using hk

/-- Inserting a smooth enlarged annular projection is an exact identity
for the actual periodic half-wave. -/
theorem periodicHalfWave_preproject {n : ℕ} {φ ψ : Space n → ℂ}
    (hψ : HasCompactSupport ψ) (hψφ : ∀ ξ ∈ tsupport φ, ψ ξ = 1)
    {h : ℝ} (hh : 0 < h) (t : ℝ) (f : UnitAddTorus (Fin n) → ℂ) :
    periodicHalfWave φ h t (periodicHalfWave ψ h 0 f) = periodicHalfWave φ h t f := by
  funext x
  change (∑' k, periodicSymbol φ h t k *
      UnitAddTorus.mFourierCoeff (periodicHalfWave ψ h 0 f) k * UnitAddTorus.mFourier k x) =
    ∑' k, periodicSymbol φ h t k * UnitAddTorus.mFourierCoeff f k * UnitAddTorus.mFourier k x
  apply tsum_congr
  intro k
  rw [mFourierCoeff_periodic_cutoff hψ hh]
  by_cases hφk : φ (h • periodicFrequency k) = 0
  · simp [periodicSymbol, hφk]
  · rw [hψφ _ (subset_tsupport φ hφk), one_mul]

theorem exists_enlarged_annular_projection {n : ℕ} {φ : Space n → ℂ}
    (hc : HasCompactSupport φ) (hz : 0 ∉ tsupport φ) :
    ∃ ψ : Space n → ℂ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      0 ∉ tsupport ψ ∧ ∀ ξ ∈ tsupport φ, ψ ξ = 1 := by
  obtain ⟨ψ, hψ, hcψ, hsψ, heψ⟩ := OAI.Analysis.PDE.Concentration.exists_compact_complex_cutoff hc
    (isOpen_compl_singleton : IsOpen ({0}ᶜ : Set (Space n))) (by
      intro ξ hξ
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
        (show ξ ≠ 0 from fun he => hz (he ▸ hξ)))
  refine ⟨ψ, hψ, hcψ, ?_, heψ⟩
  intro h0
  simpa using hsψ h0

theorem inverse_kernel_norm_lt_top {n : ℕ} {ψ : Space n → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    eLpNorm (𝓕⁻ ψ) 1 volume < ⊤ := by
  have he : ((𝓕⁻ (hcψ.toSchwartzMap hψ) : SchwartzMap (Space n) ℂ) : Space n → ℂ) =
      𝓕⁻ ψ := by rw [SchwartzMap.fourierInv_coe]; rfl
  rw [← he]
  exact (𝓕⁻ (hcψ.toSchwartzMap hψ)).memLp 1 |>.eLpNorm_lt_top

/-- Fixed enlarged projection with both a uniform `Lᵖ` bound and the
uniform logarithmic amplitude count used in sector assembly. -/
theorem uniform_preprojection {n : ℕ} {φ : Space n → ℂ}
    (hc : HasCompactSupport φ) (hz : 0 ∉ tsupport φ) :
    ∃ (ψ : Space n → ℂ) (B D : ℝ),
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ 0 ∉ tsupport ψ ∧
      (∀ ξ ∈ tsupport φ, ψ ξ = 1) ∧ 1 ≤ B ∧ 0 < D ∧
      ∀ h : ℝ, 0 < h → h ≤ 1 →
        ∃ N : ℕ, (N + 1 : ℝ) ≤ D * (1 + Real.log h⁻¹) ∧
          ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ → ∀ f : UnitAddTorus (Fin n) → ℂ,
            Measurable f → Integrable f → eLpNorm f p volume ≤ 1 →
            eLpNorm (periodicHalfWave ψ h 0 f) p volume ≤ ENNReal.ofReal B ∧
            (∀ x, ‖periodicHalfWave ψ h 0 f x‖ < (2 : ℝ) ^ N) ∧
            ∀ t, periodicHalfWave φ h t (periodicHalfWave ψ h 0 f) = periodicHalfWave φ h t f := by
  obtain ⟨ψ, hψ, hcψ, hzψ, heψ⟩ := exists_enlarged_annular_projection hc hz
  obtain ⟨D, hD, hcount⟩ := periodic_projected_amplitude_count hψ.continuous hcψ
  let B := (eLpNorm (𝓕⁻ ψ) 1 volume).toReal + 1
  have hB : 1 ≤ B := by dsimp [B]; linarith [ENNReal.toReal_nonneg (a := eLpNorm (𝓕⁻ ψ) 1 volume)]
  have hk : eLpNorm (𝓕⁻ ψ) 1 volume ≤ ENNReal.ofReal B := by
    rw [← ENNReal.ofReal_toReal (inverse_kernel_norm_lt_top hψ hcψ).ne]
    apply ENNReal.ofReal_le_ofReal
    dsimp [B]
    linarith
  refine ⟨ψ, B, D, hψ, hcψ, hzψ, heψ, hB, hD, ?_⟩
  intro h hh hh1
  obtain ⟨N, hN, hNf⟩ := hcount h hh hh1
  refine ⟨N, hN, ?_⟩
  intro p hp hpt f hf hfi hfn
  refine ⟨?_, hNf p hp f hfi hfn, fun t => periodicHalfWave_preproject hcψ heψ hh t f⟩
  exact (periodic_cutoff_norm_bound hcψ hψ hzψ hh hf hfi hp hpt).trans
    (by simpa only [mul_one] using mul_le_mul' hk hfn)

end OAI.Analysis.Fourier.WavePackets
