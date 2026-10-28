import OAI.Analysis.Normed.Function.Sobolev.WeakFourier

open OAI.Analysis.Fourier.Wave

open Set _root_.MeasureTheory FourierTransform Filter InnerProductSpace
open scoped Topology
noncomputable section
namespace OAI.Analysis.Normed.Function.Sobolev

open OAI.Analysis.PDE.Weak

theorem norm_realFourier_le {d : ℕ} (u : Space d → ℝ) (ξ : Space d) :
    ‖realFourier u ξ‖ ≤ ∫ x, ‖u x‖ := by
  rw [realFourier, fourier_eq_kernel]
  calc
    ‖∫ x, (u x : ℂ) * fourierKernel ξ x‖ ≤
        ∫ x, ‖(u x : ℂ) * fourierKernel ξ x‖ := norm_integral_le_integral_norm _
    _ = ∫ x, ‖u x‖ := by simp

/-- Iteration of the genuine weak Fourier derivative identity, using only
the finitely many derivatives that are actually provided. -/
theorem realFourier_iterated_weakDerivative {d k : ℕ} (v : Space d)
    (U : ℕ → Space d → ℝ) {K : Set (Space d)} (hK : IsCompact K)
    (hUK : ∀ j ≤ k, ∀ᵐ x, x ∉ K → U j x = 0)
    (hUi : ∀ j ≤ k, Integrable (U j))
    (hUD : ∀ j < k, OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivative volume v (U j) (U (j + 1)))
    (ξ : Space d) :
    realFourier (U k) ξ =
      (2 * Real.pi * Complex.I * (inner ℝ v ξ : ℂ)) ^ k * realFourier (U 0) ξ := by
  have hi (j : ℕ) : j ≤ k → realFourier (U j) ξ =
      (2 * Real.pi * Complex.I * (inner ℝ v ξ : ℂ)) ^ j * realFourier (U 0) ξ := by
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hjk : j < k := Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hj
      rw [realFourier_weakDerivative (hUD j hjk) hK (hUK j hjk.le) (hUK (j + 1) hj)
        (hUi j hjk.le) (hUi (j + 1) hj), ih hjk.le, pow_succ]
      ring
  exact hi k le_rfl

theorem norm_multiplier_iterated_weakDerivative {d k : ℕ} (v : Space d)
    (U : ℕ → Space d → ℝ) {K : Set (Space d)} (hK : IsCompact K)
    (hUK : ∀ j ≤ k, ∀ᵐ x, x ∉ K → U j x = 0)
    (hUi : ∀ j ≤ k, Integrable (U j))
    (hUD : ∀ j < k, OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivative volume v (U j) (U (j + 1)))
    (ξ : Space d) :
    (2 * Real.pi * |inner ℝ v ξ|) ^ k * ‖realFourier (U 0) ξ‖ ≤ ∫ x, ‖U k x‖ := by
  have he := congrArg norm (realFourier_iterated_weakDerivative v U hK hUK hUi hUD ξ)
  have he' : ‖realFourier (U k) ξ‖ =
      (2 * Real.pi * |inner ℝ v ξ|) ^ k * ‖realFourier (U 0) ξ‖ := by
    simpa only [norm_mul, norm_pow, Complex.norm_I, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one] using he
  rw [← he']
  exact norm_realFourier_le (U k) ξ

end OAI.Analysis.Normed.Function.Sobolev
