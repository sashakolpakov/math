import Mathlib

/-!
Exact exponent calculations in `sections/consequences.tex`.
These lemmas supply the interpolation parameters for mixed spherical
extension and the admissible radial exponents for transfer to the cone.
-/

namespace OAI.Analysis.SpecialFunctions.ConjugateExponent

/-- The conjugate exponent of a finite real exponent greater than one. -/
noncomputable def conjugateExponent (a : ℝ) : ℝ := a / (a - 1)

theorem conjugateExponent_pos {a : ℝ} (ha : 1 < a) :
    0 < conjugateExponent a :=
  div_pos (by linarith) (by linarith)

theorem one_div_conjugateExponent {a : ℝ} (ha : 1 < a) :
    1 / conjugateExponent a = 1 - 1 / a := by
  unfold conjugateExponent
  have h0 : a ≠ 0 := by linarith
  field_simp

/-- Parameters chosen in the proof of the mixed spherical extension estimate. -/
theorem mixed_extension_parameters {n a b : ℝ}
    (hn : 1 < n) (ha : 1 < a) (hab : a < b)
    (hboundary : (n + 1) / (n - 1) * conjugateExponent a < b) :
    let s := 1 + b / conjugateExponent a
    let θ := s / b
    2 * n / (n - 1) < s ∧ s < b ∧ 0 < θ ∧ θ < 1 ∧
      1 - θ + θ / s = 1 / a ∧ θ / s = 1 / b := by
  dsimp
  have hb : 0 < b := by linarith
  have hn0 : n - 1 ≠ 0 := by linarith
  have ha0 : a ≠ 0 := by linarith
  have haq : 0 < conjugateExponent a := conjugateExponent_pos ha
  have hq : (n + 1) / (n - 1) < b / conjugateExponent a :=
    (lt_div_iff₀ haq).2 hboundary
  have hpc : 2 * n / (n - 1) = 1 + (n + 1) / (n - 1) := by
    field_simp
    ; ring
  have hcrit : 2 * n / (n - 1) < 1 + b / conjugateExponent a := by
    rw [hpc]
    linarith
  have hs : 0 < 1 + b / conjugateExponent a := by positivity
  have hsmall : 1 + b / conjugateExponent a < b := by
    rw [div_eq_mul_one_div, one_div_conjugateExponent ha]
    have : 1 < b / a := (one_lt_div (by linarith : 0 < a)).2 hab
    nlinarith [show b * (1 / a) = b / a by ring]
  have ht : (1 + b / conjugateExponent a) / b / (1 + b / conjugateExponent a) =
      1 / b := by field_simp
  refine ⟨hcrit, hsmall, div_pos hs hb, (div_lt_one hb).2 hsmall, ?_, ht⟩
  · rw [ht]
    rw [div_eq_mul_one_div b, one_div_conjugateExponent ha]
    field_simp
    ; ring

/-- The cone transfer uses Hausdorff--Young at `b > 2`. -/
theorem cone_output_exponent_gt_two {n b : ℝ} (hn : 1 < n)
    (hb : 2 * n / (n - 1) < b) : 2 < b := by
  have hcrit : 2 < 2 * n / (n - 1) := by
    apply (lt_div_iff₀ (by linarith : 0 < n - 1)).2
    linarith
  exact hcrit.trans hb

/-- The strict mixed extension condition also gives the radial Hölder range. -/
theorem cone_radial_exponent {n a b : ℝ} (hn : 1 < n) (ha : 1 < a)
    (hb : (n + 1) / (n - 1) * conjugateExponent a < b) :
    conjugateExponent a < b := by
  have hc : 1 < (n + 1) / (n - 1) := by
    apply (one_lt_div (by linarith : 0 < n - 1)).2
    linarith
  have hq := conjugateExponent_pos ha
  nlinarith

end OAI.Analysis.SpecialFunctions.ConjugateExponent
