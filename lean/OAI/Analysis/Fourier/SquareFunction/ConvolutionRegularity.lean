import OAI.Analysis.Fourier.SquareFunction.KernelTail

open OAI.Analysis.Fourier.Wave

/-! Regularity of the actual convolutions entering the finite-vector sharp
argument. In particular its `L¹` hypothesis follows from kernel decay. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set
open scoped ENNReal Convolution

noncomputable def convolveKernel {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (K : Space n → H) (f : Space n → ℂ) (x : Space n) : H :=
  ∫ y, f y • K (x - y)

theorem integrable_convolveKernel {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    {K : Space n → H} {f : Space n → ℂ} (hf : Integrable f) (hK : Integrable K) :
    Integrable (convolveKernel K f) :=
  hf.integrable_convolution (L := ContinuousLinearMap.lsmul ℂ ℂ) hK

theorem continuous_convolveKernel {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    {K : Space n → H} {f : Space n → ℂ} (hf : Integrable f)
    (hK : Continuous K) (hB : BddAbove (range fun x => ‖K x‖)) :
    Continuous (convolveKernel K f) :=
  hB.continuous_convolution_right_of_integrable (L := ContinuousLinearMap.lsmul ℂ ℂ) hf hK

theorem integrable_convolveKernel_integrand {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    {K : Space n → H} {f : Space n → ℂ} (hf : Integrable f)
    (hK : Continuous K) (hB : BddAbove (range fun x => ‖K x‖)) (x : Space n) :
    Integrable (fun y => f y • K (x - y)) := by
  have hb : BddAbove ((fun i => ‖K i‖) '' ((fun t => x - t) ⁻¹' univ)) := by
    simpa only [preimage_univ, image_univ] using hB
  exact hb.convolutionExistsAt (L := ContinuousLinearMap.lsmul ℂ ℂ) MeasurableSet.univ
    (subset_univ _) hf.integrableOn hK.aestronglyMeasurable

theorem norm_convolveKernel_le {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    {K : Space n → H} {f : Space n → ℂ} (hf : Integrable f)
    (hK : Continuous K) {B : ℝ} (hB : ∀ x, ‖K x‖ ≤ B) (x : Space n) :
    ‖convolveKernel K f x‖ ≤ (∫ y, ‖f y‖) * B := by
  have hbi : BddAbove (range fun x => ‖K x‖) := ⟨B, by rintro _ ⟨y, rfl⟩; exact hB y⟩
  calc
    _ ≤ ∫ y, ‖f y • K (x - y)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, ‖f y‖ * B := by
      apply integral_mono (integrable_convolveKernel_integrand hf hK hbi x).norm (hf.norm.mul_const B)
      intro y
      dsimp only
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)
    _ = _ := integral_mul_const _ _

/-- Polynomial kernel decay supplies the global first moment required to
remove the root-average error in the sharp-function argument. -/
theorem integrable_of_polynomial_decay {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] {a q C : ℝ} (ha : 0 < a) (hq : (n : ℝ) < q)
    {K : Space n → H} (hKm : AEStronglyMeasurable K)
    (hK : ∀ u, ‖K u‖ ≤ C * a ^ n * (a * ‖u‖ + 1) ^ (-q)) :
    Integrable K := by
  refine ⟨hKm, ?_⟩
  change (∫⁻ u, ‖K u‖ₑ) < ∞
  have hmass : (∫⁻ u : Space n, ENNReal.ofReal ((a * ‖u‖ + 1) ^ (-q))) < ∞ := by
    have h := polynomial_kernel_mass_scaling ha q (0 : Space n)
    simp only [dist_zero_right] at h
    rw [h]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (polynomialKernelMass_lt_top hq)
  calc
    _ ≤ ∫⁻ u, ENNReal.ofReal (C * a ^ n) * ENNReal.ofReal ((a * ‖u‖ + 1) ^ (-q)) := by
      apply lintegral_mono
      intro u
      have h := ENNReal.ofReal_le_ofReal (hK u)
      rw [ofReal_norm, ENNReal.ofReal_mul' (Real.rpow_nonneg (by positivity) _)] at h
      exact h
    _ = ENNReal.ofReal (C * a ^ n) * ∫⁻ u : Space n, ENNReal.ofReal ((a * ‖u‖ + 1) ^ (-q)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmass

theorem bounded_of_polynomial_decay {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] {a q C : ℝ} (ha : 0 ≤ a) (hq : 0 ≤ q) (hC : 0 ≤ C)
    {K : Space n → H}
    (hK : ∀ u, ‖K u‖ ≤ C * a ^ n * (a * ‖u‖ + 1) ^ (-q)) :
    ∀ u, ‖K u‖ ≤ C * a ^ n := by
  intro u
  calc
    _ ≤ C * a ^ n * (a * ‖u‖ + 1) ^ (-q) := hK u
    _ ≤ C * a ^ n * 1 := mul_le_mul_of_nonneg_left
      (Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [mul_nonneg ha (norm_nonneg u)])
        (neg_nonpos.mpr hq)) (mul_nonneg hC (pow_nonneg ha _))
    _ = _ := mul_one _

/-- Exact local/tail splitting of the actual convolution, justified by
integrability of both summands. -/
theorem convolveKernel_indicator_add_compl {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    {K : Space n → H} {f : Space n → ℂ} (hf : Integrable f)
    (hK : Continuous K) (hB : BddAbove (range fun x => ‖K x‖))
    {P : Set (Space n)} (hP : MeasurableSet P) (x : Space n) :
    convolveKernel K f x = convolveKernel K (P.indicator f) x +
      convolveKernel K (Pᶜ.indicator f) x := by
  rw [convolveKernel, convolveKernel, convolveKernel, ← integral_add
    (integrable_convolveKernel_integrand (hf.indicator hP) hK hB x)
    (integrable_convolveKernel_integrand (hf.indicator hP.compl) hK hB x)]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : y ∈ P <;> simp [hy]

end OAI.Analysis.Fourier.SquareFunction
