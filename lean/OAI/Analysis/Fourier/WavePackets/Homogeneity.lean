import OAI.Analysis.Fourier.WavePackets.Periodic
import OAI.Analysis.Fourier.Wave.Basic

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory
open scoped ENNReal

local instance homogeneityCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance homogeneityCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance homogeneityCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem periodicHalfWave_congr_ae {n : ℕ} (φ : Space n → ℂ) (h t : ℝ)
    {f g : UnitAddTorus (Fin n) → ℂ} (hfg : f =ᵐ[volume] g) :
    periodicHalfWave φ h t f = periodicHalfWave φ h t g := by
  funext x
  apply tsum_congr
  intro k
  have he : UnitAddTorus.mFourierCoeff f k = UnitAddTorus.mFourierCoeff g k := by
    apply integral_congr_ae
    filter_upwards [hfg] with y hy
    rw [hy]
  rw [he]

@[simp] theorem periodicHalfWave_zero {n : ℕ} (φ : Space n → ℂ) (h t : ℝ) :
    periodicHalfWave φ h t (0 : UnitAddTorus (Fin n) → ℂ) = 0 := by
  funext x
  simp [periodicHalfWave, UnitAddTorus.mFourierCoeff]

theorem periodicHalfWave_real_smul {n : ℕ} (φ : Space n → ℂ) (h t c : ℝ)
    (f : UnitAddTorus (Fin n) → ℂ) :
    periodicHalfWave φ h t (c • f) = c • periodicHalfWave φ h t f := by
  funext x
  have he (k : Fin n → ℤ) : UnitAddTorus.mFourierCoeff (c • f) k =
      c • UnitAddTorus.mFourierCoeff f k := by
    unfold UnitAddTorus.mFourierCoeff
    simp only [Pi.smul_apply, smul_comm (UnitAddTorus.mFourier (-k) _) c]
    exact integral_smul c _
  simp only [periodicHalfWave, he, Pi.smul_apply]
  simp only [mul_smul_comm, smul_mul_assoc, tsum_const_smul'']

/-- Remove the unit-input normalization using the genuine homogeneity and
almost-everywhere invariance of the Fourier multiplier. -/
theorem periodic_bound_of_normalized {n : ℕ} (φ : Space n → ℂ) (h : ℝ)
    (μ : Measure (ℝ × UnitAddTorus (Fin n))) {p C : ℝ≥0∞} (hp : p ≠ 0)
    (hbound : ∀ g : UnitAddTorus (Fin n) → ℂ, Measurable g → Integrable g →
      eLpNorm g p volume ≤ 1 →
      eLpNorm (fun q : ℝ × UnitAddTorus (Fin n) => periodicHalfWave φ h q.1 g q.2) p μ ≤ C)
    (f : UnitAddTorus (Fin n) → ℂ) (hf : Measurable f) (hfi : Integrable f)
    (hfp : MemLp f p volume) :
    eLpNorm (fun q : ℝ × UnitAddTorus (Fin n) => periodicHalfWave φ h q.1 f q.2) p μ ≤
      C * eLpNorm f p volume := by
  by_cases hz : eLpNorm f p volume = 0
  · have he := (eLpNorm_eq_zero_iff hp).mp hz
    have ht (t : ℝ) := periodicHalfWave_congr_ae φ h t he
    simp only [periodicHalfWave_zero] at ht
    simp [ht, hz]
  let c : ℝ := (eLpNorm f p volume).toReal
  have hc : 0 < c := ENNReal.toReal_pos hz hfp.eLpNorm_ne_top
  have hcE : ENNReal.ofReal c = eLpNorm f p volume :=
    ENNReal.ofReal_toReal hfp.eLpNorm_ne_top
  let g : UnitAddTorus (Fin n) → ℂ := c⁻¹ • f
  have hg : Measurable g := hf.const_smul _
  have hgi : Integrable g := hfi.smul _
  have hgn : eLpNorm g p volume ≤ 1 := by
    rw [show g = c⁻¹ • f from rfl, eLpNorm_const_smul]
    rw [Real.enorm_eq_ofReal (inv_nonneg.mpr hc.le),
      ENNReal.ofReal_inv_of_pos hc, hcE]
    exact (ENNReal.inv_mul_cancel hz hfp.eLpNorm_ne_top).le
  have hfg : f = c • g := by simp [g, smul_smul, hc.ne']
  have houtput : (fun q : ℝ × UnitAddTorus (Fin n) => periodicHalfWave φ h q.1 f q.2) =
      c • (fun q : ℝ × UnitAddTorus (Fin n) => periodicHalfWave φ h q.1 g q.2) := by
    funext q
    rw [hfg, periodicHalfWave_real_smul]
    rfl
  rw [houtput, eLpNorm_const_smul, Real.enorm_eq_ofReal hc.le, hcE]
  exact (mul_le_mul' le_rfl (hbound g hg hgi hgn)).trans_eq (mul_comm _ _)

end OAI.Analysis.Fourier.WavePackets
