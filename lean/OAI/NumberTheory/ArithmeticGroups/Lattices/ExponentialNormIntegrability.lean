import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Complex.Exponential

/-! # Exponential Norm Integrability -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ExponentialNormIntegrability.Construction

noncomputable section

/-! Exponential norm decay is integrable against additive Haar measure
on every finite-dimensional real normed space. -/

open Real _root_.MeasureTheory

theorem exp_neg_mul_le_inverse_power (c : ℝ) (hc : 0 < c) (N : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    Real.exp (-c * x) ≤ ((N.factorial : ℝ) / c ^ N * Real.exp c) * (1 + x) ^ (-(N : ℝ)) := by
  have hfac : 0 < (N.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos N
  have hp := Real.pow_div_factorial_le_exp (c * (1 + x)) (by positivity) N
  have hp' : (1 + x) ^ N ≤ ((N.factorial : ℝ) / c ^ N) * Real.exp (c * (1 + x)) := by
    have he := (div_le_iff₀ hfac).mp hp
    rw [mul_pow] at he
    have hb : (1 + x) ^ N ≤ Real.exp (c * (1 + x)) * N.factorial / c ^ N :=
      (le_div_iff₀ (pow_pos hc N)).mpr (by simpa only [mul_comm] using he)
    calc
      _ ≤ _ := hb
      _ = _ := by ring
  have hprod : Real.exp (c * (1 + x)) * Real.exp (-c * x) = Real.exp c := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h := mul_le_mul_of_nonneg_right hp' (Real.exp_pos (-c * x)).le
  rw [mul_assoc, hprod] at h
  rw [Real.rpow_neg (by positivity : 0 ≤ 1 + x), Real.rpow_natCast, ← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1 + x) N)).mpr
  simpa only [mul_comm] using h

theorem integrable_exp_neg_mul_norm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (c : ℝ) (hc : 0 < c) : Integrable (fun x : E => Real.exp (-c * ‖x‖)) μ := by
  let N := Module.finrank ℝ E + 1
  have hN : (Module.finrank ℝ E : ℝ) < (N : ℝ) := by dsimp [N]; norm_cast; omega
  have hp : Integrable (fun x : E => (1 + ‖x‖) ^ (-(N : ℝ))) μ := integrable_one_add_norm hN
  let C := (N.factorial : ℝ) / c ^ N * Real.exp c
  apply (hp.const_mul C).mono'
    (Real.continuous_exp.comp (continuous_const.mul continuous_norm)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  change ‖Real.exp (-c * ‖x‖)‖ ≤ C * (1 + ‖x‖) ^ (-(N : ℝ))
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact exp_neg_mul_le_inverse_power c hc N ‖x‖ (norm_nonneg x)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ExponentialNormIntegrability.Construction
