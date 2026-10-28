import OAI.Analysis.Fourier.SquareFunction.BoundaryPartialSums
import OAI.Analysis.Fourier.SquareFunction.BoundaryWeights
import OAI.Analysis.Fourier.SquareFunction.Amplitude.Profile
import OAI.Analysis.Fourier.SquareFunction.FourierSeries

open OAI.Analysis.Fourier.Wave

/-! Identification of the singular boundary series with the actual inverse
Fourier integral. Integrability is needed only at almost every radius. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory FourierTransform Set Filter
open scoped ENNReal Topology

noncomputable def boundaryRadiusDerivative {n : ℕ} (α r : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) : ℂ :=
  𝓕⁻ (fun ξ : Space n => (radiusMultiplier α ‖ξ‖ r : ℂ) *
    (OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff (4 * (r - ‖ξ‖)) : ℂ) * (𝓕 f) ξ) x

theorem dyadicShellWidth_power_coefficient (J j : ℕ) (a : ℝ) :
    dyadicShellWidth J j ^ a = ((2 : ℝ) ^ (J + j)) ^ (-a) := by
  rw [← inv_dyadicShellWidth, Real.inv_rpow (dyadicShellWidth_pos J j).le,
    Real.rpow_neg (dyadicShellWidth_pos J j).le, inv_inv]

noncomputable def boundaryShellSymbol {n : ℕ} (A : ℝ × Space n → ℂ)
    (α r : ℝ) (f : SchwartzMap (Space n) ℂ) (j : ℕ) (ξ : Space n) : ℂ :=
  Complex.ofReal (((2 : ℝ) ^ (2 + j)) ^ (-(α - 1))) * A (r, ξ) *
    OAI.Analysis.Fourier.BochnerRiesz.dyadicPowerProfile (α - 1) ((2 : ℝ) ^ (2 + j) * (r - ‖ξ‖)) *
      (𝓕 f : SchwartzMap (Space n) ℂ) ξ

theorem integrable_boundaryShellSymbol {n : ℕ} {A : ℝ × Space n → ℂ}
    (hA : Continuous A) (hc : HasCompactSupport A) (α r : ℝ)
    (f : SchwartzMap (Space n) ℂ) (j : ℕ) :
    Integrable (boundaryShellSymbol A α r f j) := by
  have hp := (OAI.Analysis.Fourier.BochnerRiesz.dyadicPowerProfile (α - 1)).continuous
  have hf := (𝓕 f).continuous
  apply Continuous.integrable_of_hasCompactSupport (by unfold boundaryShellSymbol; fun_prop)
  apply HasCompactSupport.of_support_subset_isCompact (hc.image continuous_snd)
  intro ξ hξ
  refine ⟨(r, ξ), subset_tsupport A ?_, rfl⟩
  intro hz
  exact hξ (by simp only [boundaryShellSymbol, hz, mul_zero, zero_mul])

theorem norm_sum_boundaryShellSymbol {n : ℕ} {A : ℝ × Space n → ℂ} {α r : ℝ}
    (hr1 : 1 ≤ r) (hr2 : r ≤ 2)
    (ha : ∀ ξ : Space n, 1 / 2 ≤ ‖ξ‖ → ‖ξ‖ ≤ 2 →
      A (r, ξ) = (2 * α * ‖ξ‖ ^ 2 * r ^ (-2 * α) * (r + ‖ξ‖) ^ (α - 1) : ℝ))
    (f : SchwartzMap (Space n) ℂ) (N : ℕ) (ξ : Space n) :
    ‖∑ j ∈ Finset.range N, boundaryShellSymbol A α r f j ξ‖ ≤
      ‖(radiusMultiplier α ‖ξ‖ r : ℂ) * (𝓕 f) ξ‖ := by
  simp only [boundaryShellSymbol, ← Finset.sum_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right
    (norm_radiusMultiplier_boundary_partial_sum (norm_nonneg ξ) hr1 hr2 (A (r, ξ))
      (ha ξ) (by norm_num) N) (norm_nonneg _)

theorem boundaryShellSymbol_hasSum {n : ℕ} {A : ℝ × Space n → ℂ} {α r : ℝ}
    (hr1 : 1 ≤ r) (hr2 : r ≤ 2)
    (ha : ∀ ξ : Space n, 1 / 2 ≤ ‖ξ‖ → ‖ξ‖ ≤ 2 →
      A (r, ξ) = (2 * α * ‖ξ‖ ^ 2 * r ^ (-2 * α) * (r + ‖ξ‖) ^ (α - 1) : ℝ))
    (f : SchwartzMap (Space n) ℂ) (ξ : Space n) :
    HasSum (fun j => boundaryShellSymbol A α r f j ξ)
      ((radiusMultiplier α ‖ξ‖ r : ℂ) *
        (OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff (4 * (r - ‖ξ‖)) : ℂ) *
          (𝓕 f : SchwartzMap (Space n) ℂ) ξ) := by
  have H := hasSum_radiusMultiplier_boundary (norm_nonneg ξ) hr1 hr2 (A (r, ξ)) (ha ξ)
  exact H.mul_right ((𝓕 f : SchwartzMap (Space n) ℂ) ξ)

theorem boundaryRadiusDerivative_tendsto {n : ℕ} {A : ℝ × Space n → ℂ}
    (hA : Continuous A) (hc : HasCompactSupport A) {α r : ℝ}
    (hr1 : 1 ≤ r) (hr2 : r ≤ 2)
    (ha : ∀ ξ : Space n, 1 / 2 ≤ ‖ξ‖ → ‖ξ‖ ≤ 2 →
      A (r, ξ) = (2 * α * ‖ξ‖ ^ 2 * r ^ (-2 * α) * (r + ‖ξ‖) ^ (α - 1) : ℝ))
    (f : SchwartzMap (Space n) ℂ)
    (hi : Integrable (fun ξ : Space n => (radiusMultiplier α ‖ξ‖ r : ℂ) * (𝓕 f) ξ))
    (x : Space n) :
    Tendsto (fun N => ∑ j ∈ Finset.range N,
      Complex.ofReal (dyadicShellWidth 2 j ^ (α - 1)) *
        amplitudeShellRadiusMap A hA (OAI.Analysis.Fourier.BochnerRiesz.dyadicPowerProfile (α - 1))
          (dyadicShellWidth 2 j) f x ⟨r, hr1, hr2⟩)
      atTop (𝓝 (boundaryRadiusDerivative α r f x)) := by
  let u := boundaryShellSymbol A α r f
  have H := tendsto_sum_fourierInv_of_dominated (n := n) (u := u)
    (v := fun ξ : Space n => (radiusMultiplier α ‖ξ‖ r : ℂ) *
      (OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff (4 * (r - ‖ξ‖)) : ℂ) *
        (𝓕 f : SchwartzMap (Space n) ℂ) ξ)
    (B := fun ξ : Space n => ‖(radiusMultiplier α ‖ξ‖ r : ℂ) *
      (𝓕 f : SchwartzMap (Space n) ℂ) ξ‖)
    (integrable_boundaryShellSymbol hA hc α r f) hi.norm
    (fun N => Eventually.of_forall (norm_sum_boundaryShellSymbol hr1 hr2 ha f N))
    (Eventually.of_forall fun ξ => (boundaryShellSymbol_hasSum hr1 hr2 ha f ξ).tendsto_sum_nat) x
  have he (j : ℕ) : 𝓕⁻ (u j) x =
      Complex.ofReal (dyadicShellWidth 2 j ^ (α - 1)) *
        amplitudeShellRadiusMap A hA (OAI.Analysis.Fourier.BochnerRiesz.dyadicPowerProfile (α - 1))
          (dyadicShellWidth 2 j) f x ⟨r, hr1, hr2⟩ := by
    rw [amplitudeShellRadiusMap_apply A hA hc]
    simp only [fourierInv_eq_spatialPhase_smul, smul_eq_mul, u, boundaryShellSymbol,
      dyadicShellWidth_power_coefficient]
    rw [← integral_const_mul]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro ξ
    dsimp only
    rw [div_eq_mul_inv, inv_dyadicShellWidth]
    simp only [mul_comm (r - ‖ξ‖) ((2 : ℝ) ^ (2 + j)), ← SchwartzMap.fourier_coe]
    ring
  simpa only [he, boundaryRadiusDerivative] using H

theorem ae_integrable_radius_symbol_schwartz {n : ℕ} [NeZero n] {α : ℝ}
    (hα : 1 / 2 < α) (f : SchwartzMap (Space n) ℂ) :
    ∀ᵐ r ∂volume.restrict (Ioi 0),
      Integrable (fun ξ : Space n => (radiusMultiplier α ‖ξ‖ r : ℂ) * (𝓕 f) ξ) := by
  let f₂ : OAI.Analysis.Fourier.Wave.WaveL2 n := f.toLp 2 volume
  have hF : (Lp.fourierTransformₗᵢ (Space n) ℂ) f₂ = (𝓕 f).toLp 2 := by
    change 𝓕 (f.toLp 2) = (𝓕 f).toLp 2
    exact SchwartzMap.toLp_fourier_eq f
  filter_upwards [ae_memLp_radius_symbol hα f₂] with r hr
  apply integrable_radius_symbol (n := n) α r
    ((𝓕 f : SchwartzMap (Space n) ℂ) : Space n → ℂ)
  have hcoe : (fun ξ : Space n => (radiusMultiplier α ‖ξ‖ r : ℂ) *
      ((Lp.fourierTransformₗᵢ (Space n) ℂ) f₂) ξ) =ᵐ[volume]
      (fun ξ : Space n => (radiusMultiplier α ‖ξ‖ r : ℂ) * (𝓕 f) ξ) := by
    rw [hF]
    filter_upwards [(𝓕 f).coeFn_toLp 2 volume] with ξ hξ
    rw [hξ]
  exact (memLp_congr_ae hcoe).mp hr

end OAI.Analysis.Fourier.SquareFunction
