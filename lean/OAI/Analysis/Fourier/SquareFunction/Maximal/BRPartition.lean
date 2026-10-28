import OAI.Analysis.Fourier.BochnerRiesz.OperatorPartition

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform Filter
open scoped ENNReal ContDiff Topology
noncomputable section
namespace OAI.Analysis.Fourier.SquareFunction


def brScaledInterior {n : ℕ} (δ : ℝ) (J : ℕ) (h : ℝ)
    (f : SchwartzMap (Space n) ℂ) : Space n → ℂ :=
  𝓕⁻ (fun ξ : Space n => OAI.Analysis.Fourier.BochnerRiesz.brInteriorSymbol δ J (h • ((2 * Real.pi) • ξ)) *
    (𝓕 f : SchwartzMap (Space n) ℂ) ξ)

def brScaledPacket {n : ℕ} (δ : ℝ) (χ : Space n → ℂ) (j : ℕ) (h : ℝ)
    (f : SchwartzMap (Space n) ℂ) : Space n → ℂ :=
  𝓕⁻ (fun ξ : Space n => OAI.Analysis.Fourier.BochnerRiesz.brExteriorSymbol δ χ (h • ((2 * Real.pi) • ξ)) *
    (OAI.Analysis.Fourier.BochnerRiesz.dyadicPowerProfile δ ((2 : ℝ) ^ j - (h * (2 * Real.pi) * (2 : ℝ) ^ j) * ‖ξ‖) *
      (𝓕 f : SchwartzMap (Space n) ℂ) ξ))

theorem integrable_scaled_smooth_cycles_mul {n : ℕ} {a b : Space n → ℂ}
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) {h : ℝ} (hh : 0 < h)
    (hb : Integrable b) :
    Integrable (fun ξ : Space n => a (h • ((2 * Real.pi) • ξ)) * b ξ) := by
  apply OAI.Analysis.Fourier.BochnerRiesz.integrable_smooth_cycles_mul (a := fun ξ => a (h • ξ))
    (by fun_prop) (hc.comp_smul hh.ne') hb

theorem brScaledInterior_finite_partition {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {J : ℕ} (hJ : 2 ≤ J) {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hzero : 0 ∉ tsupport χ)
    (hone : ∀ ξ, 1 / 2 ≤ ‖ξ‖ → ‖ξ‖ ≤ 2 → χ ξ = 1)
    {h : ℝ} (hh : 0 < h) (N : ℕ) (f : SchwartzMap (Space n) ℂ) :
    brScaledInterior δ (J + N) h f = fun x => brScaledInterior δ J h f x +
      ∑ j ∈ Finset.range N, Complex.ofReal (((2 : ℝ) ^ (J + j)) ^ (-δ)) *
        brScaledPacket δ χ (J + j) h f x := by
  have ha := OAI.Analysis.Fourier.BochnerRiesz.contDiff_brExteriorSymbol δ hχ hzero
  have hca := OAI.Analysis.Fourier.BochnerRiesz.hasCompactSupport_brExteriorSymbol δ hc
  let b (j : ℕ) (ξ : Space n) : ℂ := OAI.Analysis.Fourier.BochnerRiesz.brExteriorSymbol δ χ (h • ((2 * Real.pi) • ξ)) *
    (OAI.Analysis.Fourier.BochnerRiesz.dyadicPowerProfile δ ((2 : ℝ) ^ (J + j) -
      (h * (2 * Real.pi) * (2 : ℝ) ^ (J + j)) * ‖ξ‖) *
      (𝓕 f : SchwartzMap (Space n) ℂ) ξ)
  have hb (j : ℕ) : Integrable (b j) :=
    integrable_scaled_smooth_cycles_mul ha hca hh (OAI.Analysis.Fourier.BochnerRiesz.integrable_dilatedShellSymbol _ _ _ f)
  have he : (fun ξ : Space n => OAI.Analysis.Fourier.BochnerRiesz.brInteriorSymbol δ (J + N) (h • ((2 * Real.pi) • ξ)) *
      (𝓕 f : SchwartzMap (Space n) ℂ) ξ) = fun ξ =>
      OAI.Analysis.Fourier.BochnerRiesz.brInteriorSymbol δ J (h • ((2 * Real.pi) • ξ)) * (𝓕 f : SchwartzMap (Space n) ℂ) ξ +
        ∑ j ∈ Finset.range N, Complex.ofReal (((2 : ℝ) ^ (J + j)) ^ (-δ)) * b j ξ := by
    funext ξ
    rw [OAI.Analysis.Fourier.BochnerRiesz.brInteriorSymbol, ← OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz_symbol_finite_partition hδ hJ hone N]
    rw [add_mul, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [b]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hh,
      abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    rw [show (2 : ℝ) ^ (J + j) * (1 - h * (2 * Real.pi * ‖ξ‖)) =
      (2 : ℝ) ^ (J + j) - (h * (2 * Real.pi) * (2 : ℝ) ^ (J + j)) * ‖ξ‖ by ring]
    ring
  change 𝓕⁻ _ = _
  rw [he, OAI.Analysis.Fourier.BochnerRiesz.fourierInv_add_integrable
    (integrable_scaled_smooth_cycles_mul (OAI.Analysis.Fourier.BochnerRiesz.contDiff_brInteriorSymbol hδ hJ)
      (OAI.Analysis.Fourier.BochnerRiesz.hasCompactSupport_brInteriorSymbol hδ J) hh (𝓕 f).integrable)
    (integrable_finsetSum _ (fun j _ => (hb j).const_mul _)),
    OAI.Analysis.Fourier.BochnerRiesz.fourierInv_finset_sum _ _ (fun j _ => (hb j).const_mul _)]
  simp_rw [OAI.Analysis.Fourier.BochnerRiesz.fourierInv_const_mul]
  rfl

theorem continuous_brScaledInterior {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {J : ℕ} (hJ : 2 ≤ J) {h : ℝ} (hh : 0 < h) (f : SchwartzMap (Space n) ℂ) :
    Continuous (brScaledInterior δ J h f) :=
  OAI.Analysis.Fourier.BochnerRiesz.continuous_fourierInv_of_integrable (integrable_scaled_smooth_cycles_mul
    (OAI.Analysis.Fourier.BochnerRiesz.contDiff_brInteriorSymbol hδ hJ) (OAI.Analysis.Fourier.BochnerRiesz.hasCompactSupport_brInteriorSymbol hδ J) hh (𝓕 f).integrable)

theorem tendsto_brScaledInterior {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {J : ℕ} (hJ : 2 ≤ J) {R : ℝ} (hR : 0 < R) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    Tendsto (fun N : ℕ => brScaledInterior δ (J + N) R⁻¹ f x) atTop
      (𝓝 (OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f x)) := by
  rw [OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz_eq_fourierInv]
  refine OAI.Analysis.Fourier.BochnerRiesz.tendsto_fourierInv_bounded_symbols
    (m := fun N ξ => OAI.Analysis.Fourier.BochnerRiesz.brInteriorSymbol δ (J + N) (R⁻¹ • ((2 * Real.pi) • ξ)))
    (C := 1) ?_ ?_ (𝓕 f).integrable ?_ x
  · intro N
    apply Continuous.aestronglyMeasurable
    exact (OAI.Analysis.Fourier.BochnerRiesz.contDiff_brInteriorSymbol hδ (show 2 ≤ J + N by omega)).continuous.comp
      (by fun_prop)
  · intro N ξ
    rw [OAI.Analysis.Fourier.BochnerRiesz.brInteriorSymbol, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (OAI.Analysis.Fourier.BochnerRiesz.brInteriorReal_mem_Icc hδ.le (J + N) _).1]
    exact (OAI.Analysis.Fourier.BochnerRiesz.brInteriorReal_mem_Icc hδ.le (J + N) _).2
  · intro ξ
    have H := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (OAI.Analysis.Fourier.BochnerRiesz.tendsto_brInteriorReal hδ J (R⁻¹ • ((2 * Real.pi) • ξ)))
    have he : OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszCyclesSymbol δ R ξ =
        (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol δ 1 (R⁻¹ • ((2 * Real.pi) • ξ)) : ℂ) := by
      simp only [OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszCyclesSymbol, OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hR), div_eq_mul_inv, inv_one, one_mul, mul_comm]
    simpa only [OAI.Analysis.Fourier.BochnerRiesz.brInteriorSymbol, Function.comp_def, he] using H

theorem measurable_bochnerRieszMaximal {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (f : SchwartzMap (Space n) ℂ) : Measurable (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszMaximal δ f) := by
  apply LowerSemicontinuous.measurable
  apply lowerSemicontinuous_iSup
  intro R
  apply lowerSemicontinuous_iSup
  intro hR
  exact (OAI.Analysis.Fourier.BochnerRiesz.continuous_bochnerRiesz_schwartz hδ R f).enorm.lowerSemicontinuous

end OAI.Analysis.Fourier.SquareFunction
