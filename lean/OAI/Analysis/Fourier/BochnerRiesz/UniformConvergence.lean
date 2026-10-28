import OAI.Analysis.Fourier.BochnerRiesz.BoundedFamily
import OAI.Analysis.Fourier.Restriction.Interpolation

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform Filter
open scoped ENNReal Topology
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz


def brFourierError {n : ℕ} (δ R : ℝ) (f : SchwartzMap (Space n) ℂ) : ℝ :=
  ∫ ξ, ‖(bochnerRieszCyclesSymbol δ R ξ - 1) * (𝓕 f : SchwartzMap (Space n) ℂ) ξ‖

theorem integrable_brFourierError_integrand {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (R : ℝ) (f : SchwartzMap (Space n) ℂ) :
    Integrable (fun ξ => (bochnerRieszCyclesSymbol δ R ξ - 1) *
      (𝓕 f : SchwartzMap (Space n) ℂ) ξ) := by
  have H := (integrable_bochnerRieszSymbol_mul hδ R _ (𝓕 f).integrable).sub (𝓕 f).integrable
  convert H using 1
  ext ξ
  simp only [Pi.sub_apply, sub_mul, one_mul]

theorem brFourierError_nonneg {n : ℕ} (δ R : ℝ) (f : SchwartzMap (Space n) ℂ) :
    0 ≤ brFourierError δ R f := integral_nonneg (fun _ => norm_nonneg _)

theorem norm_bochnerRiesz_sub_le_fourierError {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (R : ℝ) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    ‖OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f x - f x‖ ≤ brFourierError δ R f := by
  have he : f x = 𝓕⁻ (fun ξ => (𝓕 f : SchwartzMap (Space n) ℂ) ξ) x := by
    rw [← SchwartzMap.fourierInv_coe, fourierInv_fourier_eq]
  rw [he, bochnerRiesz_eq_fourierInv, OAI.Analysis.Fourier.SquareFunction.fourierInv_eq_spatialPhase_smul,
    OAI.Analysis.Fourier.SquareFunction.fourierInv_eq_spatialPhase_smul,
    ← integral_sub (OAI.Analysis.Fourier.SquareFunction.integrable_spatialPhase_smul x
      (integrable_bochnerRieszSymbol_mul hδ R _ (𝓕 f).integrable))
      (OAI.Analysis.Fourier.SquareFunction.integrable_spatialPhase_smul x (𝓕 f).integrable)]
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  apply Eventually.of_forall
  intro ξ
  simp only [SchwartzMap.fourier_coe, ← smul_sub, ← sub_one_mul,
    norm_smul, OAI.Analysis.Fourier.SquareFunction.norm_spatialPhase, one_mul]

theorem tendsto_brFourierError {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (f : SchwartzMap (Space n) ℂ) :
    Tendsto (fun R : ℝ => brFourierError δ R f) atTop (𝓝 0) := by
  have H : Tendsto (fun R : ℝ => ∫ ξ, ‖(bochnerRieszCyclesSymbol δ R ξ - 1) *
      (𝓕 f : SchwartzMap (Space n) ℂ) ξ‖) atTop (𝓝 (∫ ξ : Space n, (0 : ℝ))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun ξ => 2 * ‖(𝓕 f : SchwartzMap (Space n) ℂ) ξ‖)
    · exact Eventually.of_forall fun R =>
        (integrable_brFourierError_integrand hδ R f).norm.aestronglyMeasurable
    · apply Eventually.of_forall
      intro R
      apply Eventually.of_forall
      intro ξ
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      have H : ‖bochnerRieszCyclesSymbol δ R ξ - 1‖ ≤ ‖bochnerRieszCyclesSymbol δ R ξ‖ + 1 := by
        simpa only [norm_one] using norm_sub_le (bochnerRieszCyclesSymbol δ R ξ) 1
      have hm := norm_bochnerRieszCyclesSymbol_le hδ R ξ
      linarith
    · exact (𝓕 f).integrable.norm.const_mul 2
    · apply Eventually.of_forall
      intro ξ
      have ht := Complex.continuous_ofReal.continuousAt.tendsto.comp
        (OAI.Analysis.Fourier.SquareFunction.tendsto_bochnerRieszSymbol_radius hδ ((2 * Real.pi) • ξ))
      have H := ((ht.sub (tendsto_const_nhds (x := (1 : ℂ)))).mul
        (tendsto_const_nhds (x := (𝓕 f : SchwartzMap (Space n) ℂ) ξ))).norm
      simpa only [bochnerRieszCyclesSymbol, Complex.ofReal_one, sub_self,
        zero_mul, norm_zero, Function.comp_def] using H
  simpa only [brFourierError, integral_zero] using H

/-- A uniform lower-exponent estimate upgrades Fourier dominated convergence
to strong convergence at every strictly larger finite exponent. -/
theorem tendsto_eLpNorm_bochnerRiesz_sub_of_lower_bound {n : ℕ} {δ q p : ℝ}
    (hδ : 0 ≤ δ) (hq : 1 ≤ q) (hqp : q < p) (f : SchwartzMap (Space n) ℂ)
    {C : ℝ} (_ : 0 ≤ C)
    (hbound : ∀ R : ℝ, 0 < R → eLpNorm (OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f) (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal q) volume) :
    Tendsto (fun R : ℝ => eLpNorm (fun x => OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f x - f x)
      (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hp0 : 0 < p := hq0.trans hqp
  let B : ℝ≥0∞ := (ENNReal.ofReal C + 1) * eLpNorm f (ENNReal.ofReal q) volume
  have hB : B ≠ ⊤ := ENNReal.mul_ne_top (by finiteness) (f.memLp _ volume).ne
  have hlow (R : ℝ) (hR : 0 < R) :
      eLpNorm (fun x => OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f x - f x) (ENNReal.ofReal q) volume ≤ B := by
    calc
      _ ≤ eLpNorm (OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f) (ENNReal.ofReal q) volume +
          eLpNorm f (ENNReal.ofReal q) volume := by
        exact eLpNorm_sub_le (by simpa using ENNReal.ofReal_le_ofReal hq)
      _ ≤ ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal q) volume +
          eLpNorm f (ENNReal.ofReal q) volume := add_le_add (hbound R hR) le_rfl
      _ = B := by dsimp [B]; rw [add_mul, one_mul]
  have hpow : 0 < (p - q) / p := div_pos (sub_pos.mpr hqp) hp0
  have ht := (ENNReal.continuous_rpow_const (y := (p - q) / p)).continuousAt.tendsto.comp
    (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (tendsto_brFourierError hδ f))
  have ht' : Tendsto (fun R : ℝ => (ENNReal.ofReal (brFourierError δ R f)) ^ ((p - q) / p) *
      B ^ (q / p)) atTop (𝓝 0) := by
    have hbpow : B ^ (q / p) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (div_nonneg hq0.le hp0.le) hB
    have H := ENNReal.Tendsto.const_mul ht (Or.inr hbpow)
    simpa only [Function.comp_def, ENNReal.ofReal_zero,
      ENNReal.zero_rpow_of_pos hpow, mul_zero, zero_mul, mul_comm] using H
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht'
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have H := OAI.Analysis.Fourier.Restriction.eLpNorm_le_of_enorm_bound volume (B := ENNReal.ofReal (brFourierError δ R f))
    ((continuous_bochnerRiesz_schwartz hδ R f).sub f.continuous).aestronglyMeasurable hq0 hqp.le
    (Eventually.of_forall fun x => by
      simpa only [ofReal_norm, Pi.sub_apply] using
        ENNReal.ofReal_le_ofReal (norm_bochnerRiesz_sub_le_fourierError hδ R f x))
  exact H.trans (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (hlow R hR) (div_nonneg hq0.le hp0.le)))

end OAI.Analysis.Fourier.BochnerRiesz
