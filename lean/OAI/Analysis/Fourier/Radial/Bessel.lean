import OAI.Analysis.Fourier.Radial.Asymptotic

/-! Conversion of the radial Bessel equation into an inverse-square
perturbation of the harmonic oscillator. -/

open Set Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.Fourier.Radial

def besselNormalize (m : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ := t ^ m * f t

def besselNormalizeDeriv (m : ℝ) (f g : ℝ → ℝ) (t : ℝ) : ℝ :=
  t ^ m * g t + m * t ^ (m - 1) * f t

theorem hasDerivAt_besselNormalize {m t : ℝ} {f g : ℝ → ℝ}
    (ht : 0 < t) (hf : HasDerivAt f (g t) t) :
    HasDerivAt (besselNormalize m f) (besselNormalizeDeriv m f g t) t := by
  have hp : HasDerivAt (fun r : ℝ => r ^ m) (m * t ^ (m - 1)) t := by
    simpa using (hasDerivAt_id t).rpow_const (p := m) (Or.inl ht.ne')
  unfold besselNormalize besselNormalizeDeriv
  convert hp.mul hf using 1 ; ring

theorem hasDerivAt_besselNormalizeDeriv {m t : ℝ} {f g : ℝ → ℝ}
    (ht : 0 < t) (hf : HasDerivAt f (g t) t)
    (hg : HasDerivAt g (-2 * m / t * g t - f t) t) :
    HasDerivAt (besselNormalizeDeriv m f g)
      ((m * (m - 1) / t ^ 2 - 1) * besselNormalize m f t) t := by
  have hp (a : ℝ) : HasDerivAt (fun r : ℝ => r ^ a) (a * t ^ (a - 1)) t := by
    simpa using (hasDerivAt_id t).rpow_const (p := a) (Or.inl ht.ne')
  have H := ((hp m).mul hg).add (((hp (m - 1)).mul hf).const_mul m)
  have h1 : t ^ (m - 1) = t ^ m / t := by rw [Real.rpow_sub ht, Real.rpow_one]
  have h2 : t ^ (m - 1 - 1) = t ^ m / t ^ 2 := by
    rw [show m - 1 - 1 = m - 2 by ring, Real.rpow_sub ht, Real.rpow_two]
  unfold besselNormalize besselNormalizeDeriv
  convert H using 1
  · funext r
    simp only [Pi.add_apply, Pi.mul_apply]
    ring
  · rw [h1, h2]
    field_simp
    ; ring

theorem bessel_normalized_asymptotic {m : ℝ} {f g : ℝ → ℝ}
    (hf : ∀ t, 1 ≤ t → HasDerivAt f (g t) t)
    (hg : ∀ t, 1 ≤ t → HasDerivAt g (-2 * m / t * g t - f t) t)
    (hne : f 1 ≠ 0 ∨ g 1 ≠ 0) :
    ∃ A B C : ℝ, 0 ≤ C ∧ 0 < A ^ 2 + B ^ 2 ∧ ∀ r, 1 ≤ r →
      |r ^ m * f r - (A * Real.cos r + B * Real.sin r)| ≤ C / r ∧
      |r ^ m * g r + m * r ^ (m - 1) * f r -
        (-A * Real.sin r + B * Real.cos r)| ≤ C / r := by
  apply oscillator_asymptotic
    (fun t ht => hasDerivAt_besselNormalize (by linarith) (hf t ht))
    (fun t ht => hasDerivAt_besselNormalizeDeriv (by linarith) (hf t ht) (hg t ht))
  simp only [oscillatorEnergy, besselNormalize, besselNormalizeDeriv, Real.one_rpow, one_mul]
  rcases hne with h | h
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h) (sq_nonneg _)
  · by_cases h0 : f 1 = 0
    · simp only [h0, mul_zero, add_zero, zero_pow two_ne_zero, zero_add]
      exact sq_pos_of_ne_zero h
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h0) (sq_nonneg _)

end OAI.Analysis.Fourier.Radial
