import OAI.Analysis.PDE.Concentration.GaussianJets

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory Set
open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- Scaling the argument of the genuine Gaussian costs only one power
of the scale per derivative, even when its argument is arbitrarily large. -/
theorem gaussian_scaled_composition_bound (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ : E → F, ContDiff ℝ ∞ ψ → ∀ B : ℝ, 1 ≤ B →
      ∀ scale : ℝ, 1 ≤ scale → ∀ n ≤ N, ∀ x : E,
      (∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j ψ x‖ ≤ B) →
      ‖iteratedFDeriv ℝ n (fun y => standardGaussian (scale • ψ y)) x‖ ≤
        (n.factorial : ℝ) * C * B ^ n * scale ^ n := by
  obtain ⟨C, hC, hc⟩ := standardGaussian_bounded_jets (E := F) N
  refine ⟨C, hC, ?_⟩
  intro ψ hψ B hB scale hscale n hn x hx
  have hs : ContDiff ℝ ∞ (fun y => scale • ψ y) := hψ.const_smul scale
  have hb := norm_iteratedFDeriv_comp_le (contDiff_standardGaussian (E := F)) hs (by simp) x
    (fun j hj => hc j (hj.trans hn) _)
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

theorem sqrt_pow_eq_half_rpow {L : ℝ} (hL : 0 ≤ L) (n : ℕ) :
    Real.sqrt L ^ n = L ^ ((n : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hL]
  congr 1
  ring

/-- The derivative loss for a Gaussian phase at logarithmic scale `L` is
`L^(n/2)`, the count required in the restricted-sector estimate. -/
theorem gaussian_logarithmic_composition_bound (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ : E → F, ContDiff ℝ ∞ ψ → ∀ B : ℝ, 1 ≤ B →
      ∀ L : ℝ, 1 ≤ L → ∀ n ≤ N, ∀ x : E,
      (∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j ψ x‖ ≤ B) →
      ‖iteratedFDeriv ℝ n (fun y => standardGaussian (Real.sqrt L • ψ y)) x‖ ≤
        (n.factorial : ℝ) * C * B ^ n * L ^ ((n : ℝ) / 2) := by
  obtain ⟨C, hC, hc⟩ := gaussian_scaled_composition_bound (E := E) (F := F) N
  refine ⟨C, hC, ?_⟩
  intro ψ hψ B hB L hL n hn x hx
  have hs : 1 ≤ Real.sqrt L := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hL
  have hb := hc ψ hψ B hB (Real.sqrt L) hs n hn x hx
  rwa [sqrt_pow_eq_half_rpow (by linarith : 0 ≤ L)] at hb

end OAI.Analysis.PDE.Concentration
