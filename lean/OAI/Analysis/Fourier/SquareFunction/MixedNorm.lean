import OAI.Analysis.Fourier.WavePackets.Young
import OAI.Analysis.Fourier.LocalSmoothing.L2

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal

noncomputable section
namespace OAI.Analysis.Fourier.SquareFunction

section MixedNorm

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]

omit [SFinite μ] in
/-- Hölder in the inner variable, followed by Tonelli. -/
theorem mixed_square_energy_le {F : X × Y → ℝ≥0∞} (hF : Measurable F)
    {p : ℝ} (hp : 2 ≤ p) :
    (∫⁻ x, (∫⁻ y, F (x, y) ^ (2 : ℝ) ∂ν) ^ (p / 2) ∂μ) ≤
      ν univ ^ (p / 2 - 1) * ∫⁻ z, F z ^ p ∂μ.prod ν := by
  calc
    _ ≤ ∫⁻ x, ν univ ^ (p / 2 - 1) * (∫⁻ y, F (x, y) ^ p ∂ν) ∂μ := by
      apply lintegral_mono
      intro x
      have h := OAI.Analysis.Fourier.WavePackets.lintegral_rpow_le_mass_mul
        (ν := ν) ((hF.comp ((measurable_const (a := x)).prodMk measurable_id)).pow_const (2 : ℝ))
        (p := p / 2) (by linarith)
      simpa only [← ENNReal.rpow_mul, show (2 : ℝ) * (p / 2) = p by ring,
        Function.comp_apply, id_eq]
        using h
    _ = ν univ ^ (p / 2 - 1) * ∫⁻ z, F z ^ p ∂μ.prod ν := by
      rw [lintegral_const_mul'' _ (hF.pow_const p).lintegral_prod_right'.aemeasurable]
      rw [lintegral_prod _ (hF.pow_const p).aemeasurable]

omit [SFinite μ] in
/-- The norm form of the finite-time `Lᵖ` to `L²` comparison used after
Fourier transformation in the radius variable. -/
theorem mixed_square_norm_le {F : X × Y → ℝ≥0∞} (hF : Measurable F)
    {p : ℝ} (hp : 2 ≤ p) :
    (∫⁻ x, (∫⁻ y, F (x, y) ^ (2 : ℝ) ∂ν) ^ (p / 2) ∂μ) ^ (1 / p) ≤
      ν univ ^ (1 / 2 - 1 / p) * (∫⁻ z, F z ^ p ∂μ.prod ν) ^ (1 / p) := by
  have hp₀ : 0 < p := by linarith
  have h := ENNReal.rpow_le_rpow (mixed_square_energy_le μ ν hF hp)
    (show 0 ≤ 1 / p by positivity)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul] at h
  have he : (p / 2 - 1) * (1 / p) = 1 / 2 - 1 / p := by field_simp
  simpa only [he] using h

def mixedSquareNorm (F : X × Y → ℂ) (p : ℝ) : ℝ≥0∞ :=
  (∫⁻ x, (∫⁻ y, ‖F (x, y)‖ₑ ^ (2 : ℝ) ∂ν) ^ (p / 2) ∂μ) ^ (1 / p)

omit [SFinite μ] in
theorem mixedSquareNorm_le_eLpNorm {F : X × Y → ℂ} (hF : Measurable F)
    {p : ℝ} (hp : 2 ≤ p) :
    mixedSquareNorm μ ν F p ≤
      ν univ ^ (1 / 2 - 1 / p) * eLpNorm F (ENNReal.ofReal p) (μ.prod ν) := by
  have hp₀ : 0 < p := by linarith
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top
    hF.aestronglyMeasurable, ENNReal.toReal_ofReal hp₀.le]
  exact mixed_square_norm_le μ ν hF.enorm hp

end MixedNorm

/-- The immediate mixed-norm consequence of Euclidean local smoothing on
the unit observation interval. The deeper all-radii transfer is separate. -/
theorem localSmoothing_mixedSquareNorm (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {p ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      mixedSquareNorm volume (volume.restrict (Icc 1 2))
        (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1) p ≤
      ENNReal.ofReal C *
        eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.besselPotential (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε) f) (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC, hb⟩ := hls n hn p ε hp (Or.inl hε)
  refine ⟨C, hC, fun f => ?_⟩
  have h := mixedSquareNorm_le_eLpNorm volume (volume.restrict (Icc (1 : ℝ) 2))
    (OAI.Analysis.Fourier.LocalSmoothing.continuous_halfWaveIntegral f).measurable hp
  have hm : (volume.restrict (Icc (1 : ℝ) 2)) univ = 1 := by norm_num
  rw [hm, ENNReal.one_rpow, one_mul] at h
  exact h.trans (hb f).2.2

end OAI.Analysis.Fourier.SquareFunction
