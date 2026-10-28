import OAI.Analysis.Fourier.BochnerRiesz.ProjectionDilation

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem littlewoodPaley_annular_projection_ge_two {n N : ℕ} [NeZero n] {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hband : ∀ ξ, χ ξ ≠ 0 →
      (2 : ℝ) ^ (-(N : ℤ)) ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ (2 : ℝ) ^ (N : ℤ))
    {p : ℝ} (hp : 2 ≤ p) :
    ∃ A : ℝ, 0 < A ∧ ∀ s : Finset ℤ, ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun x ↦ OAI.Analysis.Fourier.SquareFunction.vectorNorm (fun i : s ↦
        annularProject χ ((2 : ℝ) ^ (-i.val)) f x)) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal A * eLpNorm f (ENNReal.ofReal p) volume := by
  rcases lt_or_eq_of_le hp with hp | hp
  · exact littlewoodPaley_annular_projection hχ hc hband hp
  subst p
  obtain ⟨M, hM, hm⟩ := schwartz_kernel_decay (hc.toSchwartzMap hχ) 0
  have hb (ξ : Space n) : ‖χ ξ‖ ≤ M := by
    change ‖(hc.toSchwartzMap hχ) ξ‖ ≤ M
    simpa only [neg_zero, Real.rpow_zero, mul_one] using (hm ξ).1
  let B : ℝ≥0∞ := ENNReal.ofReal ((2 * (N : ℝ) + 1) * M ^ 2) ^ (1 / 2 : ℝ)
  have hB : B ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hBA : B ≤ ENNReal.ofReal (B.toReal + 1) := by
    calc
      B = ENNReal.ofReal B.toReal := (ENNReal.ofReal_toReal hB).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
  refine ⟨B.toReal + 1, by positivity, ?_⟩
  intro s f
  have H := eLpNorm_dyadicAnnularConvolution_vector_two hχ.continuous hc hband hM.le hb
    f.integrable (f.memLp 2 volume) s
  have H' := H.trans (mul_le_mul' hBA (le_refl (eLpNorm f 2 volume)))
  simpa only [← annularProject_eq_dyadicAnnularConvolution hχ hc, ENNReal.ofReal_ofNat] using H'

theorem littlewoodPaley_annular_projection_uniform_dilation_ge_two {n N : ℕ} [NeZero n] {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hband : ∀ ξ, χ ξ ≠ 0 →
      (2 : ℝ) ^ (-(N : ℤ)) ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ (2 : ℝ) ^ (N : ℤ))
    {p : ℝ} (hp : 2 ≤ p) :
    ∃ A : ℝ, 0 < A ∧ ∀ r : ℝ, 0 < r → ∀ s : Finset ℤ, ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun x ↦ OAI.Analysis.Fourier.SquareFunction.vectorNorm (fun i : s ↦
        annularProject χ (r * (2 : ℝ) ^ (-i.val)) f x)) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal A * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨A, hA, hLP⟩ := littlewoodPaley_annular_projection_ge_two hχ hc hband hp
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
