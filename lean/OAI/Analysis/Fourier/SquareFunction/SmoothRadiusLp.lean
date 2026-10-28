import OAI.Analysis.Fourier.SquareFunction.SmoothRadiusL2
import OAI.Analysis.Fourier.SquareFunction.RemainderSpectral
import OAI.Analysis.Fourier.SquareFunction.LittlewoodPaley
import OAI.Analysis.Fourier.SquareFunction.CountableSquare
import OAI.Analysis.Fourier.WavePackets.SmoothRadiusDecay
import OAI.Analysis.Fourier.BochnerRiesz.SchwartzKernel

open OAI.Analysis.Fourier.Wave

/-! The smooth remainder square function is bounded on every finite Lp,
p>2. Its aggregate L² estimate, not a sum of scalar bounds, is used here. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set
open scoped ENNReal ContDiff

noncomputable def dyadicSmoothRadiusSquare {n : ℕ} (A : ℝ × Space n → ℂ)
    (hA : Continuous A) (f : Space n → ℂ) : Space n → ℝ≥0∞ :=
  countableSquareNorm (fun k : ℤ =>
    convolveKernel (dilatedKernel (smoothRadiusKernel A hA) ((2 : ℝ) ^ k)) f)

theorem continuous_convolve_dilated_smoothRadiusKernel {n : ℕ}
    (A : ℝ × Space n → ℂ) (hA : Continuous A) (hc : HasCompactSupport A)
    {a : ℝ} (ha : 0 < a) {f : Space n → ℂ} (hf : Integrable f) :
    Continuous (convolveKernel (dilatedKernel (smoothRadiusKernel A hA) a) f) := by
  have he := funext (smoothRadiusKernel_dilate A hA ha)
  rw [← he]
  exact continuous_convolve_smoothRadiusKernel _ _
    (hasCompactSupport_radius_frequency_dilate hc ha.ne') hf

theorem dyadicSmoothRadiusSquare_bound {n : ℕ} [NeZero n] {A : ℝ × Space n → ℂ}
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A) {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (henergy : ∀ s : Finset ℤ, ∀ ξ : Space n, ∑ k ∈ s, ∫⁻ r in Icc (1 : ℝ) 2,
      ‖A (r, ((2 : ℝ) ^ k)⁻¹ • ξ)‖ₑ ^ (2 : ℝ) ≤ M)
    {p : ℝ} (hp : 2 < p) :
    ∃ D : ℝ≥0∞, D ≠ ⊤ ∧ ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (dyadicSmoothRadiusSquare A hA.continuous f) (ENNReal.ofReal p) volume ≤
        D * eLpNorm f (ENNReal.ofReal p) volume := by
  let : MeasurableSpace RadiusHilbert := borel RadiusHilbert
  let : BorelSpace RadiusHilbert := ⟨rfl⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  obtain ⟨C, hC, hdec⟩ := OAI.Analysis.Fourier.WavePackets.smoothRadiusKernel_decay hA hc (n + 2)
  let q : ℝ := n + 2
  let K := smoothRadiusKernel A hA.continuous
  have hKd : Differentiable ℝ K := differentiable_smoothRadiusKernel A hA.continuous hc
  have hk (x : Space n) : ‖K x‖ ≤ C * (‖x‖ + 1) ^ (-q) := by
    simpa only [q, Nat.cast_add, Nat.cast_ofNat, add_comm 1 ‖x‖] using (hdec x).1
  have hk' (x : Space n) : ‖fderiv ℝ K x‖ ≤ C * (‖x‖ + 1) ^ (-q) := by
    simpa only [q, Nat.cast_add, Nat.cast_ofNat, add_comm 1 ‖x‖] using (hdec x).2
  have hB : M ^ (1 / 2 : ℝ) ≠ ⊤ := (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hM).ne
  refine ⟨commonInputLpConstant n p q C (M ^ (1 / 2 : ℝ)),
    commonInputLpConstant_ne_top hp hB, fun f => ?_⟩
  apply countableSquareNorm_bound (I := ℤ) (μ := volume) (p := p) _
    (fun k => (continuous_convolve_dilated_smoothRadiusKernel A hA.continuous hc
      (by positivity : 0 < (2 : ℝ) ^ k) f.integrable).measurable) (by linarith)
  intro s
  obtain ⟨F, hF, hfdec⟩ := OAI.Analysis.Fourier.BochnerRiesz.schwartz_kernel_decay f 0
  have hfb : BddAbove (range (fun x : Space n => ‖f x‖)) := by
    refine ⟨F, ?_⟩
    rintro y ⟨x, rfl⟩
    simpa only [neg_zero, Real.rpow_zero, mul_one] using (hfdec x).1
  apply littlewoodPaley_kernel_family s (fun i => dilatedKernel K ((2 : ℝ) ^ i.val)) f hp
    (by dsimp [q]; linarith) hC.le
    (fun i => differentiable_dilatedKernel hKd _)
    (fun i => dilatedKernel_decay (by positivity) hk)
    (fun i => dilatedKernel_derivative_decay (by positivity) hKd hk')
    f.continuous.measurable f.integrable hfb (f.memLp 2) hB
  intro g hg hg2
  exact dyadic_smoothRadiusKernel_two_bound A hA.continuous hc s M (henergy s) hg hg2

theorem dyadicRemainderSquare_bound {n : ℕ} [NeZero n] {A : ℝ × Space n → ℂ}
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A) {α p : ℝ}
    (hα : 1 / 2 < α) (hp : 2 < p)
    (hdom : ∀ r ∈ Icc (1 : ℝ) 2, ∀ ξ : Space n,
      ‖A (r, ξ)‖ₑ ≤ ‖(radiusMultiplier α ‖ξ‖ r : ℂ)‖ₑ) :
    ∃ D : ℝ≥0∞, D ≠ ⊤ ∧ ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (dyadicSmoothRadiusSquare A hA.continuous f) (ENNReal.ofReal p) volume ≤
        D * eLpNorm f (ENNReal.ofReal p) volume := by
  apply dyadicSmoothRadiusSquare_bound hA hc
    (M := 2 * ENNReal.ofReal (α / (2 * α - 1))) (by finiteness) _ hp
  intro s ξ
  simpa only [ENNReal.rpow_two] using remainder_spectral_energy_le hα A hdom s ξ

end OAI.Analysis.Fourier.SquareFunction
