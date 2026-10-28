import OAI.Analysis.Fourier.BochnerRiesz.Shell.Scales
import OAI.Analysis.Fourier.BochnerRiesz.MaximalSummation
import OAI.Analysis.Fourier.BochnerRiesz.LittlewoodPaleyEndpoint

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem shell_support_scaled_annulus {n : ℕ} (φ : SchwartzMap ℝ ℂ) (R : ℝ)
    (hR : ∀ t, φ t ≠ 0 → |t| ≤ R) {Λ r ρ : ℝ} (hΛ : 1 ≤ Λ) (hΛR : 2 * R ≤ Λ)
    (hr : 0 < r) (hρ : ρ ∈ Icc (1 : ℝ) 2) (ξ : Space n)
    (hξ : φ (Λ - (ρ * r) * ‖ξ‖) ≠ 0) :
    Real.pi / 2 ≤ ‖(Λ⁻¹ * r) • ((2 * Real.pi) • ξ)‖ ∧
      ‖(Λ⁻¹ * r) • ((2 * Real.pi) • ξ)‖ ≤ 4 * Real.pi := by
  have hΛ0 : 0 < Λ := by linarith
  have hphase : -R ≤ Λ - ρ * (r * ‖ξ‖) ∧ Λ - ρ * (r * ‖ξ‖) ≤ R := by
    simpa only [mul_assoc] using abs_le.mp (hR (Λ - (ρ * r) * ‖ξ‖) hξ)
  have hu : 0 ≤ r * ‖ξ‖ := mul_nonneg hr.le (norm_nonneg ξ)
  have hlo : Λ / 4 ≤ r * ‖ξ‖ := by
    nlinarith [mul_le_mul_of_nonneg_right hρ.2 hu]
  have hhi : r * ‖ξ‖ ≤ 2 * Λ := by
    nlinarith [mul_le_mul_of_nonneg_right hρ.1 hu]
  have he : ‖(Λ⁻¹ * r) • ((2 * Real.pi) • ξ)‖ = (2 * Real.pi * (r * ‖ξ‖)) / Λ := by
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (mul_pos (inv_pos.mpr hΛ0) hr), abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    ring
  rw [he]
  constructor
  · apply (le_div_iff₀ hΛ0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hlo (by positivity : 0 ≤ 2 * Real.pi)]
  · apply (div_le_iff₀ hΛ0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hhi (by positivity : 0 ≤ 2 * Real.pi)]

/-- The maximal thin-annulus estimate over all positive dilations. The
constant is independent of the radius-to-thickness ratio `Λ`. -/
theorem localSmoothing_maximalShellCycles (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) (φ : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (φ : ℝ → ℂ))
    {p ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ L : ℝ, 1 ≤ L ∧ ∀ Λ : ℝ, L ≤ Λ → ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (maximalShellCycles φ Λ f) (ENNReal.ofReal p) volume ∧
      eLpNorm (maximalShellCycles φ Λ f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C * Λ ^ (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε)) * eLpNorm f (ENNReal.ofReal p) volume := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall (0 : ℝ)
  have hradius : ∀ t, φ t ≠ 0 → |t| ≤ R := by
    intro t ht
    simpa only [mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hR (subset_closure ht)
  obtain ⟨C₀, hC₀, hlocal⟩ := localSmoothing_dyadicShellMax_of_support hls hn φ R hradius hp hε
  obtain ⟨χ, hχ, hcχ, hzeroχ, honeχ, hbandχ⟩ := exists_annular_cutoff (n := n)
    (a := Real.pi / 4) (b := Real.pi / 2) (c := 4 * Real.pi) (d := 8 * Real.pi)
    (by positivity) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hband : ∀ ξ, χ ξ ≠ 0 →
      (2 : ℝ) ^ (-(5 : ℤ)) ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ (2 : ℝ) ^ (5 : ℤ) := by
    intro ξ hξ
    obtain ⟨hlo, hhi⟩ := hbandχ ξ hξ
    norm_num
    constructor <;> linarith [Real.pi_gt_three, Real.pi_lt_four]
  obtain ⟨A, hA, hLP⟩ := littlewoodPaley_annular_projection_uniform_dilation_ge_two hχ hcχ (N := 5) hband hp
  refine ⟨C₀ * A, mul_pos hC₀ hA, max 1 (2 * R), le_max_left _ _, ?_⟩
  intro Λ hΛ f
  have hΛ1 : 1 ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛR : 2 * R ≤ Λ := (le_max_right _ _).trans hΛ
  have hΛ0 : 0 < Λ := by linarith
  let Q (k : ℤ) : SchwartzMap (Space n) ℂ := annularProject χ (Λ⁻¹ * (2 : ℝ) ^ (-k)) f
  let T (k : ℤ) : Space n → ℝ≥0∞ := shellBlockMax φ Λ ((2 : ℝ) ^ (-k)) f
  have hQm (k : ℤ) : Measurable (Q k : Space n → ℂ) := (Q k).continuous.measurable
  have hTm (k : ℤ) : Measurable (T k) := measurable_shellBlockMax φ Λ (by positivity) f
  have hblock (k : ℤ) : eLpNorm (T k) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (C₀ * Λ ^ (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε)) * eLpNorm (Q k) (ENNReal.ofReal p) volume := by
    have hk : 0 < (2 : ℝ) ^ (-k) := by positivity
    have hh : 0 < Λ⁻¹ * (2 : ℝ) ^ (-k) := mul_pos (inv_pos.mpr hΛ0) hk
    have hcut : ∀ ρ ∈ Icc (1 : ℝ) 2, ∀ ξ : Space n,
        φ (Λ - (ρ * (2 : ℝ) ^ (-k)) * ‖ξ‖) ≠ 0 → χ ((Λ⁻¹ * (2 : ℝ) ^ (-k)) • ((2 * Real.pi) • ξ)) = 1 := by
      intro ρ hρ ξ hξ
      obtain ⟨hlo, hhi⟩ := shell_support_scaled_annulus φ R hradius hΛ1 hΛR hk hρ ξ hξ
      exact honeχ _ hlo hhi
    have he := shellBlockMax_annularProject hχ hcχ hh φ Λ ((2 : ℝ) ^ (-k)) f hcut
    have H := eLpNorm_shellBlockMax_bound φ Λ (fun g ↦ (hlocal Λ hΛ1 hΛR g).2) hk (Q k)
    change eLpNorm (shellBlockMax φ Λ ((2 : ℝ) ^ (-k)) (annularProject χ (Λ⁻¹ * (2 : ℝ) ^ (-k)) f)) _ _ ≤ _ at H
    rw [he] at H
    exact H
  have hsquare (s : Finset ℤ) :
      eLpNorm (fun x ↦ OAI.Analysis.Fourier.SquareFunction.vectorNorm (fun i : s ↦ Q i.val x)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal A * eLpNorm f (ENNReal.ofReal p) volume := hLP Λ⁻¹ (inv_pos.mpr hΛ0) s f
  have H := eLpNorm_iSup_le_from_square_function volume T (fun k ↦ (Q k : Space n → ℂ)) hTm hQm hp hblock hsquare
  have he : maximalShellCycles φ Λ f = fun x ↦ ⨆ k : ℤ, T k x :=
    funext (maximalShellCycles_eq_iSup_blocks φ Λ f)
  have Hfinal : eLpNorm (maximalShellCycles φ Λ f) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (C₀ * A * Λ ^ (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε)) * eLpNorm f (ENNReal.ofReal p) volume := by
    rw [he]
    refine H.trans_eq ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    ring
  exact ⟨Hfinal.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (f.memLp _ volume).eLpNorm_lt_top), Hfinal⟩

end OAI.Analysis.Fourier.BochnerRiesz
