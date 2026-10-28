import OAI.Analysis.Fourier.Radial.Sphere.Asymptotic
import OAI.Analysis.Fourier.Radial.Sphere.Fourier
import OAI.Analysis.Fourier.Radial.Decay

open OAI.Analysis.Fourier.Wave

/-! Sharp Fourier decay of the standard unit-sphere surface measure. -/

open _root_.MeasureTheory
noncomputable section
namespace OAI.Analysis.Fourier.Radial

theorem sphereCosineKernel_polynomial_decay {n : ℕ} (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : Space n,
      |sphereCosineKernel x| ≤ C * (1 + ‖x‖) ^ (-((n : ℝ) - 1) / 2) := by
  obtain ⟨A, B, D, hD, _, h⟩ := sphereCosine_radial_asymptotic hn
  let M := (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real Set.univ
  let K := D + |A| + |B|
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hm : 0 ≤ ((n : ℝ) - 1) / 2 := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨(M + K + 1) * (2 : ℝ) ^ (((n : ℝ) - 1) / 2), by positivity, ?_⟩
  intro x
  convert decay_from_normalized_bound hm hM hK (norm_nonneg x)
    (abs_sphereCosineKernel_le_mass x) (fun hx => normalized_asymptotic_bound hx hD (h x hx)) using 1
  ring_nf

/-- Sharp decay for the actual angular-normalized sphere Fourier integral. -/
theorem sphericalExtension_one_polynomial_decay {n : ℕ} (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : Space n,
      ‖OAI.Analysis.Fourier.Restriction.sphericalExtension (fun _ : Space n => (1 : ℂ)) x‖ ≤
        C * (1 + ‖x‖) ^ (-((n : ℝ) - 1) / 2) := by
  obtain ⟨C, hC, h⟩ := sphereCosineKernel_polynomial_decay hn
  refine ⟨C, hC, fun x => ?_⟩
  rw [sphericalExtension_one_eq_cosine, Complex.norm_real, Real.norm_eq_abs]
  exact h x

/-- Nonzero leading radial oscillations, with a uniform normalized O(1/r)
error, for the actual sphere Fourier integral. -/
theorem sphericalExtension_one_asymptotic {n : ℕ} (hn : 1 ≤ n) :
    ∃ A B C : ℝ, 0 ≤ C ∧ 0 < A ^ 2 + B ^ 2 ∧ ∀ x : Space n, 1 ≤ ‖x‖ →
      ‖((‖x‖ ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) *
          OAI.Analysis.Fourier.Restriction.sphericalExtension (fun _ : Space n => (1 : ℂ)) x -
        ((A * Real.cos ‖x‖ + B * Real.sin ‖x‖ : ℝ) : ℂ)‖ ≤ C / ‖x‖ := by
  obtain ⟨A, B, C, hC, hAB, h⟩ := sphereCosine_radial_asymptotic hn
  refine ⟨A, B, C, hC, hAB, fun x hx => ?_⟩
  rw [sphericalExtension_one_eq_cosine, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  exact h x hx

end OAI.Analysis.Fourier.Radial
