import OAI.Analysis.Fourier.BochnerRiesz.AnnularLittlewoodPaley
import OAI.Analysis.Fourier.SquareFunction.DilationNorm

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem frequencyHalfWave_zero_dilate {n : ℕ} (χ f : Space n → ℂ) (h : ℝ)
    {r : ℝ} (hr : 0 < r) (x : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave χ h 0 (fun y ↦ f (r • y)) x =
      OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave χ (h * r) 0 f (r • x) := by
  simp only [OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave, zero_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
  let g : Space n → ℂ := fun ξ ↦ χ ((h * r) • ξ) * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ
  have he : (fun ξ ↦ χ (h • ξ) * OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun y ↦ f (r • y)) ξ) =
      fun ξ ↦ (r ^ n)⁻¹ • g (r⁻¹ • ξ) := by
    funext ξ
    rw [angularFourier_dilate f hr ξ]
    have hs : (h * r) • (r⁻¹ • ξ) = h • ξ := by
      rw [smul_smul, mul_assoc, mul_inv_cancel₀ hr.ne', mul_one]
    dsimp only [g]
    rw [hs, mul_smul_comm]
  rw [he, angularInverse_smul_real, angularInverse_dilate g (inv_pos.mpr hr)]
  simp only [inv_pow, inv_inv, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hr.ne'), one_smul]
  rfl

theorem annularProject_schwartzDilate {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) {h r : ℝ} (hh : 0 < h) (hr : 0 < r)
    (f : SchwartzMap (Space n) ℂ) :
    annularProject χ h (schwartzDilate r hr.ne' f) =
      schwartzDilate r hr.ne' (annularProject χ (h * r) f) := by
  ext x
  rw [annularProject_eq_frequencyHalfWave hχ hc hh, schwartzDilate_apply,
    annularProject_eq_frequencyHalfWave hχ hc (mul_pos hh hr)]
  exact frequencyHalfWave_zero_dilate χ f h hr x

/-- The measurable-embedding dilation formula also applies to the
extended nonnegative-valued maximal functions. -/
theorem eLpNorm_dilate_enormed {n : ℕ} {H : Type*} [TopologicalSpace H] [ContinuousENorm H]
    (f : Space n → H) (p : ℝ≥0∞) {a : ℝ} (ha : 0 < a) :
    eLpNorm (fun x ↦ f (a • x)) p (volume : Measure (Space n)) =
      ENNReal.ofReal ((a ^ n)⁻¹) ^ (1 / p.toReal) * eLpNorm f p volume := by
  have hm : MeasurableEmbedding (fun x : Space n ↦ a • x) :=
    (realDilationEquiv n a ha.ne').toHomeomorph.measurableEmbedding
  have hh := (hm.eLpNorm_map_measure (g := f) (p := p) (μ := volume)).symm
  rw [Measure.map_addHaar_smul (volume : Measure (Space n)) ha.ne'] at hh
  simp only [Space, finrank_euclideanSpace_fin, abs_of_pos (inv_pos.mpr (pow_pos ha n))] at hh
  rw [eLpNorm_smul_measure_of_ne_zero (by positivity) _ _ _] at hh
  simpa only [Function.comp_def, ENNReal.toReal_div, ENNReal.toReal_one, smul_eq_mul] using hh

theorem littlewoodPaley_annular_projection_uniform_dilation {n N : ℕ} [NeZero n] {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hband : ∀ ξ, χ ξ ≠ 0 →
      (2 : ℝ) ^ (-(N : ℤ)) ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ (2 : ℝ) ^ (N : ℤ))
    {p : ℝ} (hp : 2 < p) :
    ∃ A : ℝ, 0 < A ∧ ∀ r : ℝ, 0 < r → ∀ s : Finset ℤ, ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun x ↦ OAI.Analysis.Fourier.SquareFunction.vectorNorm (fun i : s ↦
        annularProject χ (r * (2 : ℝ) ^ (-i.val)) f x)) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal A * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨A, hA, hLP⟩ := littlewoodPaley_annular_projection hχ hc hband hp
  refine ⟨A, hA, ?_⟩
  intro r hr s f
  have H := hLP s (schwartzDilate r hr.ne' f)
  have he : (fun x ↦ OAI.Analysis.Fourier.SquareFunction.vectorNorm (fun i : s ↦
      annularProject χ ((2 : ℝ) ^ (-i.val)) (schwartzDilate r hr.ne' f) x)) =
      fun x ↦ (fun y ↦ OAI.Analysis.Fourier.SquareFunction.vectorNorm (fun i : s ↦
        annularProject χ (r * (2 : ℝ) ^ (-i.val)) f y)) (r • x) := by
    funext x
    congr 1
    funext i
    rw [annularProject_schwartzDilate hχ hc (by positivity) hr, schwartzDilate_apply, mul_comm r]
  have hd := eLpNorm_dilate_enormed (fun y ↦ OAI.Analysis.Fourier.SquareFunction.vectorNorm (fun i : s ↦
    annularProject χ (r * (2 : ℝ) ^ (-i.val)) f y)) (ENNReal.ofReal p) hr
  rw [he, hd, eLpNorm_schwartzDilate f _ hr] at H
  let D : ℝ≥0∞ := ENNReal.ofReal ((r ^ n)⁻¹) ^ (1 / (ENNReal.ofReal p).toReal)
  have hD0 : D ≠ 0 := by dsimp [D]; positivity
  have hDtop : D ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  have H' : D * eLpNorm (fun x ↦ OAI.Analysis.Fourier.SquareFunction.vectorNorm (fun i : s ↦
      annularProject χ (r * (2 : ℝ) ^ (-i.val)) f x)) (ENNReal.ofReal p) volume ≤
      D * (ENNReal.ofReal A * eLpNorm f (ENNReal.ofReal p) volume) := by
    simpa only [D, mul_left_comm, mul_assoc] using H
  have HH := mul_le_mul' (le_refl D⁻¹) H'
  simpa only [← mul_assoc, ENNReal.inv_mul_cancel hD0 hDtop, one_mul] using HH

end OAI.Analysis.Fourier.BochnerRiesz
