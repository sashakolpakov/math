import OAI.Analysis.Fourier.Radial.Kernel

open OAI.Analysis.Fourier.Wave

/-! Uniform-in-scale maximal domination for the polynomial kernel bounds used
in the low- and high-frequency parts of the combining-dilates lemma. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory
open scoped ENNReal

noncomputable def polynomialKernelMass (n : ℕ) (q : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : Space n, ENNReal.ofReal ((‖z‖ + 1) ^ (-q))

theorem polynomialKernelMass_lt_top {n : ℕ} {q : ℝ} (hq : (n : ℝ) < q) :
    polynomialKernelMass n q < ∞ := by
  have hi : Integrable (fun z : Space n => (‖z‖ + 1) ^ (-q)) := by
    simpa only [Space, finrank_euclideanSpace, Fintype.card_fin, add_comm] using
      (integrable_one_add_norm (E := Space n) (r := q) (by simpa [Space] using hq))
  have h := hi.hasFiniteIntegral
  change (∫⁻ z : Space n, ‖(‖z‖ + 1) ^ (-q)‖ₑ) < ∞ at h
  simpa only [polynomialKernelMass, Real.enorm_eq_ofReal
    (Real.rpow_nonneg (by positivity : 0 ≤ ‖(_ : Space n)‖ + 1) (-q))] using h

theorem polynomial_kernel_mass_scaling {n : ℕ} {a : ℝ} (ha : 0 < a)
    (q : ℝ) (x : Space n) :
    (∫⁻ y : Space n, ENNReal.ofReal ((a * dist y x + 1) ^ (-q))) =
      ENNReal.ofReal ((a ^ n)⁻¹) * polynomialKernelMass n q := by
  let F : Space n → ℝ≥0∞ := fun z => ENNReal.ofReal ((‖z‖ + 1) ^ (-q))
  have hF : Measurable F :=
    ((continuous_norm.measurable.add_const 1).pow_const _).ennreal_ofReal
  calc
    _ = ∫⁻ z : Space n, ENNReal.ofReal ((a * ‖z‖ + 1) ^ (-q)) := by
      simpa only [dist_eq_norm] using
        lintegral_sub_right_eq_self (μ := volume)
          (fun z : Space n => ENNReal.ofReal ((a * ‖z‖ + 1) ^ (-q))) x
    _ = ∫⁻ z : Space n, F (a • z) := by
      simp only [F, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    _ = ∫⁻ z : Space n, F z ∂Measure.map (fun z : Space n => a • z) volume :=
      (lintegral_map hF (measurable_const_smul a)).symm
    _ = _ := by
      rw [Measure.map_addHaar_smul volume ha.ne', lintegral_smul_measure]
      simp only [Space, finrank_euclideanSpace, Fintype.card_fin,
        abs_of_pos (inv_pos.mpr (pow_pos ha n)), smul_eq_mul]
      rfl

/-- Normalizing the dilated kernel cancels its change of volume exactly. -/
theorem normalized_polynomial_kernel_le_maximal {n : ℕ} {a q : ℝ}
    (ha : 0 < a) (hq : 0 < q) {f : Space n → ℝ≥0∞} (hf : Measurable f) (x : Space n) :
    (∫⁻ y, f y * (ENNReal.ofReal (a ^ n) * ENNReal.ofReal ((a * dist y x + 1) ^ (-q)))) ≤
      polynomialKernelMass n q * ballMaximal volume f x := by
  have h := OAI.Analysis.Fourier.Radial.integral_scaled_polynomial_kernel_le_maximal volume hf
    (fun x r hr => euclidean_ball_finite_pos x hr) hq ha x
  rw [polynomial_kernel_mass_scaling ha q x] at h
  calc
    _ = ENNReal.ofReal (a ^ n) *
        ∫⁻ y, f y * ENNReal.ofReal ((a * dist y x + 1) ^ (-q)) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro y
      ac_rfl
    _ ≤ ENNReal.ofReal (a ^ n) *
        (ballMaximal volume f x * (ENNReal.ofReal ((a ^ n)⁻¹) * polynomialKernelMass n q)) :=
      mul_le_mul_right h _
    _ = _ := by
      have h0 : ENNReal.ofReal (a ^ n) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (pow_pos ha n)
      rw [ENNReal.ofReal_inv_of_pos (pow_pos ha n)]
      calc
        _ = (ENNReal.ofReal (a ^ n) * (ENNReal.ofReal (a ^ n))⁻¹) *
            (polynomialKernelMass n q * ballMaximal volume f x) := by ac_rfl
        _ = _ := by rw [ENNReal.mul_inv_cancel h0 ENNReal.ofReal_ne_top, one_mul]

/-- A Hilbert-valued (indeed, Banach-valued) convolution kernel with the source's
normalized polynomial majorant is controlled pointwise by the scalar maximal
function. The estimate is uniform in the dilation parameter `a`. -/
theorem enorm_kernel_convolution_le_maximal {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    {a q C : ℝ} (ha : 0 < a) (hq : 0 < q)
    {K : Space n → H} {f : Space n → ℂ} (hf : Measurable f)
    (hK : ∀ z, ‖K z‖ₑ ≤ ENNReal.ofReal C *
      (ENNReal.ofReal (a ^ n) * ENNReal.ofReal ((a * ‖z‖ + 1) ^ (-q)))) (x : Space n) :
    ‖∫ y, f y • K (x - y)‖ₑ ≤
      ENNReal.ofReal C * (polynomialKernelMass n q *
        ballMaximal volume (fun y => ‖f y‖ₑ) x) := by
  calc
    _ ≤ ∫⁻ y, ‖f y • K (x - y)‖ₑ := enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ y, ‖f y‖ₑ * ‖K (x - y)‖ₑ := by
      apply lintegral_congr
      intro y
      exact enorm_smul _ _
    _ ≤ ∫⁻ y, ENNReal.ofReal C * (‖f y‖ₑ *
        (ENNReal.ofReal (a ^ n) * ENNReal.ofReal ((a * dist y x + 1) ^ (-q)))) := by
      apply lintegral_mono
      intro y
      calc
        _ ≤ ‖f y‖ₑ * (ENNReal.ofReal C *
            (ENNReal.ofReal (a ^ n) * ENNReal.ofReal ((a * ‖x - y‖ + 1) ^ (-q)))) :=
          mul_le_mul_right (hK (x - y)) _
        _ = _ := by rw [norm_sub_rev x y, ← dist_eq_norm]; ac_rfl
    _ = ENNReal.ofReal C * (∫⁻ y, ‖f y‖ₑ *
        (ENNReal.ofReal (a ^ n) * ENNReal.ofReal ((a * dist y x + 1) ^ (-q)))) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul_right (normalized_polynomial_kernel_le_maximal ha hq hf.enorm x) _

end OAI.Analysis.Fourier.SquareFunction
