import Mathlib

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory FourierTransform Real
open scoped FourierTransform ContDiff

theorem pow_mul_exp_neg_sq_bound (r : ℝ) (n : ℕ) :
    r ^ n * Real.exp (-(r ^ 2)) ≤ 1 + (n.factorial : ℝ) := by
  have hpow : r ^ n ≤ 1 + (r ^ 2) ^ n := by
    have he : (r ^ 2) ^ n = (r ^ n) ^ 2 := by rw [← pow_mul, ← pow_mul]; congr 1; omega
    rw [he]
    nlinarith [sq_nonneg (r ^ n - 1 / 2)]
  have ht := Real.pow_div_factorial_le_exp (r ^ 2) (sq_nonneg r) n
  have hn : (0 : ℝ) < n.factorial := by positivity
  have ht' : (r ^ 2) ^ n ≤ Real.exp (r ^ 2) * (n.factorial : ℝ) :=
    (div_le_iff₀ hn).mp ht
  have hb := mul_le_mul_of_nonneg_right ht' (Real.exp_nonneg (-(r ^ 2)))
  have hc : Real.exp (r ^ 2) * Real.exp (-(r ^ 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have he : Real.exp (-(r ^ 2)) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg r))
  have ha := mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg (-(r ^ 2)))
  calc
    _ ≤ (1 + (r ^ 2) ^ n) * Real.exp (-(r ^ 2)) := ha
    _ = Real.exp (-(r ^ 2)) + (r ^ 2) ^ n * Real.exp (-(r ^ 2)) := by ring
    _ ≤ 1 + (n.factorial : ℝ) := by
      have hh : (r ^ 2) ^ n * Real.exp (-(r ^ 2)) ≤ (n.factorial : ℝ) := by
        calc
          _ ≤ Real.exp (r ^ 2) * (n.factorial : ℝ) * Real.exp (-(r ^ 2)) := hb
          _ = (n.factorial : ℝ) := by rw [mul_right_comm, hc, one_mul]
      exact add_le_add he hh

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def standardGaussian (x : E) : ℂ := Complex.exp (-(Real.pi : ℂ) * ‖x‖ ^ 2)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem norm_standardGaussian (x : E) :
    ‖standardGaussian x‖ = Real.exp (-Real.pi * ‖x‖ ^ 2) := by
  simp [standardGaussian, Complex.norm_exp, ← Complex.ofReal_pow]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem contDiff_standardGaussian : ContDiff ℝ ∞ (standardGaussian : E → ℂ) := by
  unfold standardGaussian
  have hnorm : ContDiff ℝ ∞ (fun x : E => (‖x‖ ^ 2 : ℝ)) := contDiff_norm_sq ℝ
  convert Complex.contDiff_exp.comp ((contDiff_const (c := -(Real.pi : ℂ))).mul
    (Complex.ofRealCLM.contDiff.comp hnorm)) using 1
  simp only [Function.comp_def, Complex.ofRealCLM_apply, Complex.ofReal_pow]

theorem integrable_gaussian_moment (n : ℕ) :
    Integrable (fun x : E => ‖x‖ ^ n * ‖standardGaussian x‖) := by
  have hp : 0 < Real.pi - 1 := by linarith [Real.pi_gt_three]
  have hg := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := E) (b := ((Real.pi - 1 : ℝ) : ℂ)) (by simpa using hp) 0 (0 : E)
  have hg' : Integrable (fun x : E => Real.exp (-(Real.pi - 1) * ‖x‖ ^ 2)) := by
    simpa [Complex.norm_exp, ← Complex.ofReal_pow] using hg.norm
  apply (hg'.const_mul (1 + (n.factorial : ℝ))).mono'
    ((continuous_norm.pow n).mul contDiff_standardGaussian.continuous.norm).aestronglyMeasurable
  filter_upwards [] with x
  change ‖‖x‖ ^ n * ‖standardGaussian x‖‖ ≤ _
  rw [norm_standardGaussian, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) (Real.exp_nonneg _))]
  have he : Real.exp (-Real.pi * ‖x‖ ^ 2) =
      Real.exp (-(‖x‖ ^ 2)) * Real.exp (-(Real.pi - 1) * ‖x‖ ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (pow_mul_exp_neg_sq_bound ‖x‖ n) (Real.exp_nonneg _)

theorem fourier_standardGaussian : 𝓕 (standardGaussian : E → ℂ) = standardGaussian := by
  funext x
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hh := fourier_gaussian_innerProductSpace (V := E) (b := (Real.pi : ℂ))
    (by simpa using Real.pi_pos) x
  change 𝓕 (standardGaussian : E → ℂ) x = _ at hh
  rw [div_self hp, Complex.one_cpow, one_mul] at hh
  have he : -(Real.pi : ℂ) ^ 2 * ‖x‖ ^ 2 / Real.pi = -(Real.pi : ℂ) * ‖x‖ ^ 2 := by
    field_simp
  rw [he] at hh
  exact hh

/-- The actual Euclidean Gaussian has globally bounded derivatives of every
fixed order, obtained from its Fourier identity and integrable moments. -/
theorem standardGaussian_bounded_jets (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n ≤ N, ∀ x : E,
      ‖iteratedFDeriv ℝ n (standardGaussian : E → ℂ) x‖ ≤ C := by
  let c : ℕ → ℝ := fun n => ∫ y : E,
    ‖VectorFourier.fourierPowSMulRight (innerSL ℝ) (standardGaussian : E → ℂ) y n‖
  have hc (n : ℕ) : 0 ≤ c n := integral_nonneg fun _ => norm_nonneg _
  refine ⟨∑ n ∈ Finset.range (N + 1), c n, Finset.sum_nonneg (fun n _ => hc n), ?_⟩
  intro n hn x
  have hd := iteratedFDeriv_fourier (N := (⊤ : ℕ∞))
    (fun n _ => integrable_gaussian_moment (E := E) n)
    contDiff_standardGaussian.continuous.aestronglyMeasurable (n := n) (by simp)
  rw [fourier_standardGaussian] at hd
  rw [hd]
  have hb : ‖𝓕 (fun y : E => VectorFourier.fourierPowSMulRight (innerSL ℝ)
      (standardGaussian : E → ℂ) y n) x‖ ≤ c n :=
    VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  exact hb.trans (Finset.single_le_sum (fun i _ => hc i)
    (Finset.mem_range.mpr (by omega)))

end OAI.Analysis.PDE.Concentration
