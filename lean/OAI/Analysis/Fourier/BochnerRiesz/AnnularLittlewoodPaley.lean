import OAI.Analysis.Fourier.BochnerRiesz.AnnularKernel
import OAI.Analysis.Fourier.SquareFunction.LittlewoodPaley

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform Set
open scoped ContDiff ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

/-- The annular Littlewood--Paley upper estimate, proved using finite Fourier
overlap and the common-input sharp-function theorem. No square-function
estimate is assumed. -/
theorem littlewoodPaley_annular_convolution {n N : ℕ} [NeZero n] {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hband : ∀ ξ, χ ξ ≠ 0 →
      (2 : ℝ) ^ (-(N : ℤ)) ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ (2 : ℝ) ^ (N : ℤ))
    {p : ℝ} (hp : 2 < p) :
    ∃ A : ℝ, 0 < A ∧ ∀ s : Finset ℤ, ∀ f : Space n → ℂ,
      Measurable f → Integrable f → BddAbove (range (fun x ↦ ‖f x‖)) → MemLp f 2 →
      eLpNorm (fun x ↦ OAI.Analysis.Fourier.SquareFunction.vectorNorm (fun i : s ↦ dyadicAnnularConvolution χ i.val f x))
        (ENNReal.ofReal p) volume ≤ ENNReal.ofReal A * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨M, hM, hm⟩ := schwartz_kernel_decay (hc.toSchwartzMap hχ) 0
  have hb (ξ : Space n) : ‖χ ξ‖ ≤ M := by
    change ‖(hc.toSchwartzMap hχ) ξ‖ ≤ M
    simpa only [neg_zero, Real.rpow_zero, mul_one] using (hm ξ).1
  let q : ℝ := n + 2
  have hq : (n : ℝ) + 1 < q := by dsimp [q]; linarith
  obtain ⟨C, hC, hKd, hK⟩ := angularInverse_kernel_decay hχ hc q
  let B : ℝ≥0∞ := ENNReal.ofReal ((2 * (N : ℝ) + 1) * M ^ 2) ^ (1 / 2 : ℝ)
  have hB : B ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  let D := OAI.Analysis.Fourier.SquareFunction.commonInputLpConstant n p q C B
  have hD : D ≠ ⊤ := OAI.Analysis.Fourier.SquareFunction.commonInputLpConstant_ne_top hp hB
  have hd : D ≤ ENNReal.ofReal (D.toReal + 1) := by
    calc
      D = ENNReal.ofReal D.toReal := (ENNReal.ofReal_toReal hD).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
  refine ⟨D.toReal + 1, by positivity, ?_⟩
  intro s f hfm hfi hfb hf2
  have hkD (i : s) : Differentiable ℝ (dyadicAnnularKernel χ i.val) := by
    rw [dyadicAnnularKernel_eq_dilatedKernel]
    exact OAI.Analysis.Fourier.SquareFunction.differentiable_dilatedKernel hKd _
  have hk (i : s) (x : Space n) : ‖dyadicAnnularKernel χ i.val x‖ ≤
      C * ((2 : ℝ) ^ i.val) ^ n * ((2 : ℝ) ^ i.val * ‖x‖ + 1) ^ (-q) := by
    rw [dyadicAnnularKernel_eq_dilatedKernel]
    exact OAI.Analysis.Fourier.SquareFunction.dilatedKernel_decay (by positivity) (fun y ↦ (hK y).1) x
  have hk' (i : s) (x : Space n) : ‖fderiv ℝ (dyadicAnnularKernel χ i.val) x‖ ≤
      C * (((2 : ℝ) ^ i.val) ^ n * (2 : ℝ) ^ i.val) *
        ((2 : ℝ) ^ i.val * ‖x‖ + 1) ^ (-q) := by
    rw [dyadicAnnularKernel_eq_dilatedKernel]
    exact OAI.Analysis.Fourier.SquareFunction.dilatedKernel_derivative_decay (by positivity) hKd (fun y ↦ (hK y).2) x
  have h2 (g : Space n → ℂ) (hg : Integrable g) (hg2 : MemLp g 2) :
      eLpNorm (fun x ↦ OAI.Analysis.Fourier.SquareFunction.vectorNorm (fun i : s ↦
        OAI.Analysis.Fourier.SquareFunction.convolveKernel (dyadicAnnularKernel χ i.val) g x)) 2 volume ≤ B * eLpNorm g 2 volume := by
    simp only [convolveKernel_dyadicAnnularKernel]
    exact eLpNorm_dyadicAnnularConvolution_vector_two hχ.continuous hc hband hM.le hb hg hg2 s
  have H := OAI.Analysis.Fourier.SquareFunction.littlewoodPaley_kernel_family s (fun i ↦ dyadicAnnularKernel χ i.val) f
    hp hq hC.le hkD hk hk' hfm hfi hfb hf2 hB h2
  simp only [convolveKernel_dyadicAnnularKernel] at H
  exact H.trans (mul_le_mul' hd le_rfl)

theorem annularProject_eq_dyadicAnnularConvolution {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (k : ℤ) (f : SchwartzMap (Space n) ℂ) :
    (annularProject χ ((2 : ℝ) ^ (-k)) f : Space n → ℂ) =
      dyadicAnnularConvolution χ k f := by
  funext x
  rw [annularProject_eq_frequencyHalfWave hχ hc (by positivity)]
  exact frequencyHalfWave_zero_eq_convolution hχ.continuous hc (by positivity) f.integrable x

theorem littlewoodPaley_annular_projection {n N : ℕ} [NeZero n] {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hband : ∀ ξ, χ ξ ≠ 0 →
      (2 : ℝ) ^ (-(N : ℤ)) ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ (2 : ℝ) ^ (N : ℤ))
    {p : ℝ} (hp : 2 < p) :
    ∃ A : ℝ, 0 < A ∧ ∀ s : Finset ℤ, ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun x ↦ OAI.Analysis.Fourier.SquareFunction.vectorNorm (fun i : s ↦
        annularProject χ ((2 : ℝ) ^ (-i.val)) f x)) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal A * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨A, hA, h⟩ := littlewoodPaley_annular_convolution hχ hc hband hp
  refine ⟨A, hA, ?_⟩
  intro s f
  obtain ⟨M, hM, hm⟩ := schwartz_kernel_decay f 0
  have hfb : BddAbove (range (fun x : Space n ↦ ‖f x‖)) := by
    refine ⟨M, ?_⟩
    rintro y ⟨x, rfl⟩
    simpa only [neg_zero, Real.rpow_zero, mul_one] using (hm x).1
  simpa only [← annularProject_eq_dyadicAnnularConvolution hχ hc] using
    h s f f.continuous.measurable f.integrable hfb (f.memLp 2 volume)

end OAI.Analysis.Fourier.BochnerRiesz
