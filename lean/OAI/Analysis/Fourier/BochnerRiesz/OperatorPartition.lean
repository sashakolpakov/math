import OAI.Analysis.Fourier.BochnerRiesz.Shell.Operator
import OAI.Analysis.Fourier.BochnerRiesz.SymbolLimit
import OAI.Analysis.Fourier.BochnerRiesz.SymbolPartition
import OAI.Analysis.Fourier.BochnerRiesz.Basic

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform Filter
open scoped ENNReal ContDiff Topology
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

def brInteriorSymbol {n : ℕ} (δ : ℝ) (J : ℕ) (ξ : Space n) : ℂ :=
  brInteriorReal δ J ξ

theorem contDiff_brInteriorSymbol {n : ℕ} {δ : ℝ} (hδ : 0 < δ) {J : ℕ} (hJ : 2 ≤ J) :
    ContDiff ℝ ∞ (brInteriorSymbol (n := n) δ J) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_brInteriorReal hδ hJ)

theorem hasCompactSupport_brInteriorSymbol {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (J : ℕ) :
    HasCompactSupport (brInteriorSymbol (n := n) δ J) := by
  have he : tsupport (brInteriorSymbol (n := n) δ J) = tsupport (brInteriorReal (n := n) δ J) := by
    apply congrArg (closure : Set (Space n) → Set (Space n))
    ext ξ
    simp [Function.mem_support, brInteriorSymbol]
  unfold HasCompactSupport
  rw [he]
  exact hasCompactSupport_brInteriorReal hδ J

theorem integrable_smooth_cycles_mul {n : ℕ} {a b : Space n → ℂ}
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) (hb : Integrable b) :
    Integrable (fun ξ : Space n ↦ a ((2 * Real.pi) • ξ) * b ξ) := by
  let aS : SchwartzMap (Space n) ℂ := hc.toSchwartzMap ha
  apply integrable_mul_of_bounded_left
    (show AEStronglyMeasurable (fun ξ : Space n ↦ a ((2 * Real.pi) • ξ)) (volume : Measure (Space n)) from
      (show Continuous (fun ξ : Space n ↦ a ((2 * Real.pi) • ξ)) from by fun_prop).aestronglyMeasurable)
    (show 0 ≤ SchwartzMap.seminorm ℝ 0 0 aS from by positivity)
    (fun ξ ↦ SchwartzMap.norm_le_seminorm ℝ aS _) hb

def brInteriorCycles {n : ℕ} (δ : ℝ) (J : ℕ) (f : SchwartzMap (Space n) ℂ) : Space n → ℂ :=
  𝓕⁻ (fun ξ : Space n ↦ brInteriorSymbol δ J ((2 * Real.pi) • ξ) * (𝓕 f : SchwartzMap (Space n) ℂ) ξ)

def brShellPacket {n : ℕ} (δ : ℝ) (χ : Space n → ℂ) (j : ℕ)
    (f : SchwartzMap (Space n) ℂ) : Space n → ℂ :=
  𝓕⁻ (fun ξ : Space n ↦ brExteriorSymbol δ χ ((2 * Real.pi) • ξ) *
    (dyadicPowerProfile δ ((2 : ℝ) ^ j - (2 * Real.pi * (2 : ℝ) ^ j) * ‖ξ‖) *
      (𝓕 f : SchwartzMap (Space n) ℂ) ξ))

theorem bochnerRiesz_unit_fourierInv {n : ℕ} (δ : ℝ) (f : SchwartzMap (Space n) ℂ) :
    OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ 1 f = 𝓕⁻ (fun ξ : Space n ↦
      (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol δ 1 ((2 * Real.pi) • ξ) : ℂ) * (𝓕 f : SchwartzMap (Space n) ℂ) ξ) := by
  funext x
  rw [OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz, OAI.Analysis.Fourier.Wave.angularInverse_eq_fourierInv_scaled]
  apply Real.fourierInv_congr_ae
  filter_upwards [] with ξ
  rw [Complex.real_smul, OAI.Analysis.Fourier.Wave.angularFourier_scaled]
  rfl

theorem brInteriorCycles_finite_partition {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {J : ℕ} (hJ : 2 ≤ J) {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hzero : 0 ∉ tsupport χ)
    (hone : ∀ ξ, 1 / 2 ≤ ‖ξ‖ → ‖ξ‖ ≤ 2 → χ ξ = 1)
    (N : ℕ) (f : SchwartzMap (Space n) ℂ) :
    brInteriorCycles δ (J + N) f = fun x ↦ brInteriorCycles δ J f x +
      ∑ j ∈ Finset.range N, Complex.ofReal (((2 : ℝ) ^ (J + j)) ^ (-δ)) * brShellPacket δ χ (J + j) f x := by
  have ha := contDiff_brExteriorSymbol δ hχ hzero
  have hca := hasCompactSupport_brExteriorSymbol δ hc
  let b (j : ℕ) (ξ : Space n) : ℂ := brExteriorSymbol δ χ ((2 * Real.pi) • ξ) *
    (dyadicPowerProfile δ ((2 : ℝ) ^ (J + j) - (2 * Real.pi * (2 : ℝ) ^ (J + j)) * ‖ξ‖) *
      (𝓕 f : SchwartzMap (Space n) ℂ) ξ)
  have hb (j : ℕ) : Integrable (b j) :=
    integrable_smooth_cycles_mul ha hca (integrable_dilatedShellSymbol _ _ _ f)
  have he : (fun ξ : Space n ↦ brInteriorSymbol δ (J + N) ((2 * Real.pi) • ξ) *
      (𝓕 f : SchwartzMap (Space n) ℂ) ξ) = fun ξ ↦
      brInteriorSymbol δ J ((2 * Real.pi) • ξ) * (𝓕 f : SchwartzMap (Space n) ℂ) ξ +
        ∑ j ∈ Finset.range N, Complex.ofReal (((2 : ℝ) ^ (J + j)) ^ (-δ)) * b j ξ := by
    funext ξ
    rw [brInteriorSymbol, ← bochnerRiesz_symbol_finite_partition hδ hJ hone N]
    rw [add_mul, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [b]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    rw [show (2 : ℝ) ^ (J + j) * (1 - 2 * Real.pi * ‖ξ‖) =
      (2 : ℝ) ^ (J + j) - (2 * Real.pi * (2 : ℝ) ^ (J + j)) * ‖ξ‖ by ring]
    ring
  change 𝓕⁻ _ = _
  rw [he, fourierInv_add_integrable
    (integrable_smooth_cycles_mul (contDiff_brInteriorSymbol hδ hJ)
      (hasCompactSupport_brInteriorSymbol hδ J) (𝓕 f).integrable)
    (integrable_finsetSum _ (fun j _ ↦ (hb j).const_mul _)),
    fourierInv_finset_sum _ _ (fun j _ ↦ (hb j).const_mul _)]
  simp_rw [fourierInv_const_mul]
  rfl

theorem continuous_brInteriorCycles {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {J : ℕ} (hJ : 2 ≤ J) (f : SchwartzMap (Space n) ℂ) :
    Continuous (brInteriorCycles δ J f) :=
  continuous_fourierInv_of_integrable (integrable_smooth_cycles_mul
    (contDiff_brInteriorSymbol hδ hJ) (hasCompactSupport_brInteriorSymbol hδ J) (𝓕 f).integrable)

theorem continuous_bochnerRiesz_schwartz {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (R : ℝ) (f : SchwartzMap (Space n) ℂ) : Continuous (OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f) := by
  rw [bochnerRiesz_eq_fourierInv]
  exact continuous_fourierInv_of_integrable (integrable_bochnerRieszSymbol_mul hδ R
    (⇑(𝓕 f : SchwartzMap (Space n) ℂ)) (𝓕 f).integrable)

theorem tendsto_brInteriorCycles {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {J : ℕ} (hJ : 2 ≤ J) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    Tendsto (fun N : ℕ ↦ brInteriorCycles δ (J + N) f x) atTop (𝓝 (OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ 1 f x)) := by
  rw [bochnerRiesz_unit_fourierInv]
  refine tendsto_fourierInv_bounded_symbols
    (m := fun N ξ ↦ brInteriorSymbol δ (J + N) ((2 * Real.pi) • ξ))
    (C := 1) ?_ ?_ (𝓕 f).integrable ?_ x
  · intro N
    apply Continuous.aestronglyMeasurable
    exact (contDiff_brInteriorSymbol hδ (show 2 ≤ J + N by omega)).continuous.comp
      (show Continuous (fun ξ : Space n ↦ (2 * Real.pi) • ξ) from by fun_prop)
  · intro N ξ
    rw [brInteriorSymbol, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (brInteriorReal_mem_Icc hδ.le (J + N) _).1]
    exact (brInteriorReal_mem_Icc hδ.le (J + N) _).2
  · intro ξ
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_brInteriorReal hδ J ((2 * Real.pi) • ξ))

theorem eLpNorm_brInteriorCycles_le {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {J : ℕ} (hJ : 2 ≤ J) (f : SchwartzMap (Space n) ℂ) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpt : p ≠ ⊤) :
    eLpNorm (brInteriorCycles δ J f) p volume ≤
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse (brInteriorSymbol (n := n) δ J)) 1 volume * eLpNorm f p volume := by
  have H := eLpNorm_frequencyHalfWave_zero_le
    (contDiff_brInteriorSymbol hδ hJ).continuous (hasCompactSupport_brInteriorSymbol hδ J)
    (show (0 : ℝ) < 1 by norm_num) f.integrable hp hpt
  rw [frequencyHalfWave_zero_eq_fourierInv] at H
  rw [← SchwartzMap.fourier_coe] at H
  simpa only [one_smul, brInteriorCycles, SchwartzMap.fourier_coe] using H

end OAI.Analysis.Fourier.BochnerRiesz
