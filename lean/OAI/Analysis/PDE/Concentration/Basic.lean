import Mathlib

/-! Real inequalities in the concentration argument of `sections/concentration.tex`. -/

namespace OAI.Analysis.PDE.Concentration

/-- The conditional density in the real time coordinate at Brownian time `s`. -/
noncomputable def gaussianDensity (T s : ℝ) : ℝ :=
  Real.exp (-(T ^ 2) / (2 * s)) / Real.sqrt (2 * Real.pi * s)

/-- On the stopping-time window `[1,L²]`, the density on the observation
interval `[1,2]` is bounded below by a fixed positive constant times `L⁻¹`.
This is the last quantitative step in the cylinder harmonic-measure lemma. -/
theorem gaussianDensity_lower_bound {T s L : ℝ}
    (hT₀ : 1 ≤ T) (hT₁ : T ≤ 2) (hs₀ : 1 ≤ s) (hs₁ : s ≤ L ^ 2)
    (hL : 1 ≤ L) :
    Real.exp (-2) / (Real.sqrt (2 * Real.pi) * L) ≤ gaussianDensity T s := by
  have hs : 0 < s := by linarith
  have hLp : 0 < L := by linarith
  have hπ : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hden : 0 < Real.sqrt (2 * Real.pi * s) := Real.sqrt_pos.mpr (mul_pos hπ hs)
  have hdenL : 0 < Real.sqrt (2 * Real.pi) * L :=
    mul_pos (Real.sqrt_pos.mpr hπ) hLp
  have hT : T ^ 2 ≤ 4 := by nlinarith
  have harg : -2 ≤ -(T ^ 2) / (2 * s) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * s)).mpr
    nlinarith
  have hsqrt : Real.sqrt (2 * Real.pi * s) ≤ Real.sqrt (2 * Real.pi) * L := by
    calc
      Real.sqrt (2 * Real.pi * s) ≤ Real.sqrt (2 * Real.pi * L ^ 2) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hs₁ hπ.le)
      _ = Real.sqrt (2 * Real.pi) * L := by
        rw [Real.sqrt_mul hπ.le, Real.sqrt_sq hLp.le]
  unfold gaussianDensity
  calc
    Real.exp (-2) / (Real.sqrt (2 * Real.pi) * L) ≤
        Real.exp (-(T ^ 2) / (2 * s)) / (Real.sqrt (2 * Real.pi) * L) :=
      div_le_div_of_nonneg_right (Real.exp_le_exp.mpr harg) hdenL.le
    _ ≤ Real.exp (-(T ^ 2) / (2 * s)) / Real.sqrt (2 * Real.pi * s) :=
      div_le_div_of_nonneg_left (Real.exp_nonneg _) hden hsqrt

/-- The constant in the density bound is genuinely positive. -/
theorem gaussianDensity_lower_constant_pos :
    0 < Real.exp (-2) / Real.sqrt (2 * Real.pi) := by positivity

/-- Averaging the pointwise Gaussian bound over any distribution of stopping
times supported on `[1,L²]` preserves a lower bound proportional to its mass.
No integrability assumption is needed because this is a nonnegative integral. -/
theorem gaussian_mixture_lower_bound {ν : MeasureTheory.Measure ℝ} {T L : ℝ}
    (hT₀ : 1 ≤ T) (hT₁ : T ≤ 2) (hL : 1 ≤ L)
    (hν : ∀ᵐ s ∂ν, s ∈ Set.Icc 1 (L ^ 2)) :
    ENNReal.ofReal (Real.exp (-2) / (Real.sqrt (2 * Real.pi) * L)) * ν Set.univ ≤
      ∫⁻ s, ENNReal.ofReal (gaussianDensity T s) ∂ν := by
  calc
    _ = ∫⁻ _s, ENNReal.ofReal (Real.exp (-2) / (Real.sqrt (2 * Real.pi) * L)) ∂ν := by
      rw [MeasureTheory.lintegral_const]
    _ ≤ _ := MeasureTheory.lintegral_mono_ae (hν.mono fun s hs =>
      ENNReal.ofReal_le_ofReal (gaussianDensity_lower_bound hT₀ hT₁ hs.1 hs.2 hL))

/-- Dividing the integrated concentration estimate by the critical exponent
produces exactly the sector logarithmic loss displayed in the paper. -/
theorem concentration_logarithmic_exponent {n : ℝ} (hn : 1 < n) :
    (n + 4 + (2 * n + 4) * (n + 1) / (n - 1)) / (2 * n / (n - 1)) =
      3 * (n + 3) / 2 := by
  have hn₀ : n ≠ 0 := by linarith
  have hd : n - 1 ≠ 0 := by linarith
  field_simp
  ring

end OAI.Analysis.PDE.Concentration
