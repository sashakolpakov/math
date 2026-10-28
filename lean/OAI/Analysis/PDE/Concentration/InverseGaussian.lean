import OAI.Analysis.PDE.Concentration.GaussianScaling

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Metric
open scoped ContDiff

theorem compact_smooth_jets_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : ContDiff ℝ ∞ f) {K : Set E} (hK : IsCompact K) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n ≤ N, ∀ x ∈ K, ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
  have hb (n : ℕ) : ∃ C : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ n f x‖ ≤ C :=
    hK.exists_bound_of_continuousOn (hf.continuous_iteratedFDeriv (by simp)).continuousOn
  choose A hA using hb
  refine ⟨∑ n ∈ Finset.range (N + 1), max 0 (A n),
    Finset.sum_nonneg (fun n _ => le_max_left _ _), ?_⟩
  intro n hn x hx
  exact ((hA n x hx).trans (le_max_right _ _)).trans
    (Finset.single_le_sum (fun i _ => le_max_left _ _) (Finset.mem_range.mpr (by omega)))

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

def inverseStandardGaussian (x : F) : ℂ := Complex.exp ((Real.pi : ℂ) * ‖x‖ ^ 2)

omit [FiniteDimensional ℝ F] in
theorem contDiff_inverseStandardGaussian : ContDiff ℝ ∞ (inverseStandardGaussian : F → ℂ) := by
  unfold inverseStandardGaussian
  have hnorm : ContDiff ℝ ∞ (fun x : F => (‖x‖ ^ 2 : ℝ)) := contDiff_norm_sq ℝ
  convert Complex.contDiff_exp.comp ((contDiff_const (c := (Real.pi : ℂ))).mul
    (Complex.ofRealCLM.contDiff.comp hnorm)) using 1
  simp only [Function.comp_def, Complex.ofRealCLM_apply, Complex.ofReal_pow]

omit [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] in
theorem gaussian_mul_inverse (x : F) : standardGaussian x * inverseStandardGaussian x = 1 := by
  rw [standardGaussian, inverseStandardGaussian, ← Complex.exp_add]
  simp

/-- The reciprocal Gaussian has the same scale-per-derivative bound on a
fixed bounded patch. The patch condition is on the scaled argument. -/
theorem inverse_gaussian_scaled_composition_bound (N : ℕ) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ : E → F, ContDiff ℝ ∞ ψ → ∀ B : ℝ, 1 ≤ B →
      ∀ scale : ℝ, 1 ≤ scale → ∀ n ≤ N, ∀ x : E, ‖scale • ψ x‖ ≤ R →
      (∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j ψ x‖ ≤ B) →
      ‖iteratedFDeriv ℝ n (fun y => inverseStandardGaussian (scale • ψ y)) x‖ ≤
        (n.factorial : ℝ) * C * B ^ n * scale ^ n := by
  obtain ⟨C, hC, hc⟩ := compact_smooth_jets_bound
    (contDiff_inverseStandardGaussian (F := F)) (isCompact_closedBall (0 : F) R) N
  refine ⟨C, hC, ?_⟩
  intro ψ hψ B hB scale hscale n hn x hR hx
  have hs : ContDiff ℝ ∞ (fun y => scale • ψ y) := hψ.const_smul scale
  have hb := norm_iteratedFDeriv_comp_le contDiff_inverseStandardGaussian hs (by simp) x
    (fun j hj => hc j (hj.trans hn) _ (by simpa only [mem_closedBall, dist_zero_right] using hR))
    (D := B * scale) (fun j hj hjn => ?_)
  · simpa only [Function.comp_def, mul_pow, mul_assoc] using hb
  · change ‖iteratedFDeriv ℝ j (scale • ψ) x‖ ≤ (B * scale) ^ j
    rw [iteratedFDeriv_const_smul_apply (hψ.of_le (by simp)).contDiffAt]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ scale)]
    have hBj : B ≤ B ^ j := le_self_pow₀ hB (by omega)
    have hscalej : scale ≤ scale ^ j := le_self_pow₀ hscale (by omega)
    calc
      scale * ‖iteratedFDeriv ℝ j ψ x‖ ≤ scale * B :=
        mul_le_mul_of_nonneg_left (hx j hj hjn) (by linarith)
      _ ≤ scale ^ j * B ^ j := mul_le_mul hscalej hBj (by linarith) (by positivity)
      _ = (B * scale) ^ j := by rw [mul_pow]; ring

end OAI.Analysis.PDE.Concentration
