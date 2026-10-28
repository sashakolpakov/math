import Mathlib

/-!
Elementary transfer estimates used in `sections/transfer.tex`.
These results concern actual amplitude bounds and convergence of the dyadic
series; they do not assume a local smoothing estimate.
-/

namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory

/-- The pointwise estimate on an amplitude shell used to pass from the mixed
`L²`/`L∞` estimate to an `Lp` estimate. -/
theorem amplitude_shell_bound {a x p : ℝ} (ha : 0 ≤ a) (hax : a ≤ x)
    (hp : 2 ≤ p) : a ^ (p - 2) * x ^ 2 ≤ x ^ p := by
  have hx : 0 ≤ x := ha.trans hax
  calc
    a ^ (p - 2) * x ^ 2 ≤ x ^ (p - 2) * x ^ 2 :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ha hax (sub_nonneg.mpr hp))
        (sq_nonneg x)
    _ = x ^ p := by
      by_cases hx0 : x = 0
      · subst x
        simp [Real.zero_rpow (by linarith : p ≠ 0)]
      · rw [← Real.rpow_natCast, ← Real.rpow_add (lt_of_le_of_ne hx (Ne.symm hx0))]
        congr 1
        norm_num

/-- Integrated amplitude-shell estimate. The integration measure can already
be restricted to a shell, so the hypothesis is only almost everywhere. -/
theorem integral_amplitude_shell_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} {a p : ℝ} (ha : 0 ≤ a) (hp : 2 ≤ p)
    (hf : ∀ᵐ x ∂μ, a ≤ f x)
    (h₂ : Integrable (fun x => f x ^ 2) μ)
    (hₚ : Integrable (fun x => f x ^ p) μ) :
    a ^ (p - 2) * (∫ x, f x ^ 2 ∂μ) ≤ ∫ x, f x ^ p ∂μ := by
  rw [← integral_const_mul]
  exact integral_mono_ae (h₂.const_mul _) hₚ
    (hf.mono fun x hx => amplitude_shell_bound ha hx hp)

/-- The logarithmic Sobolev series in the last paragraph of the transfer
section converges precisely above the stated loss of one logarithm. -/
theorem logarithmic_dyadic_summable_iff (A B : ℝ) :
    Summable (fun j : ℕ => (1 + (j : ℝ)) ^ (A - B)) ↔ A + 1 < B := by
  have h := (summable_nat_add_iff 1 (f := fun j : ℕ => (j : ℝ) ^ (A - B)))
  simp only [Nat.cast_add, Nat.cast_one] at h
  rw [show (fun j : ℕ => (1 + (j : ℝ)) ^ (A - B)) =
      (fun j : ℕ => ((j : ℝ) + 1) ^ (A - B)) by
        funext j
        rw [add_comm]]
  rw [h, Real.summable_nat_rpow]
  constructor <;> intro h <;> linarith

/-- Any positive Sobolev loss absorbs the polynomial loss in the dyadic
frequency index. This is the series used for the positive-loss conclusion. -/
theorem positive_loss_dyadic_summable (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Summable (fun j : ℕ => (2 : ℝ) ^ (-(j : ℝ) * ε) * (1 + (j : ℝ)) ^ k) := by
  let r : ℝ := ε * Real.log 2
  have hr : 0 < r := mul_pos hε (Real.log_pos (by norm_num))
  have hs := (summable_nat_add_iff 1).mpr
    (Real.summable_pow_mul_exp_neg_nat_mul k hr)
  convert hs.mul_left (Real.exp r) using 1
  ext j
  simp only [Nat.cast_add, Nat.cast_one, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have he : Real.log 2 * (-(j : ℝ) * ε) = r + -r * ((j : ℝ) + 1) := by
    dsimp [r]
    ring
  rw [he, Real.exp_add]
  ring

/-- The summation step for a logarithmically weighted dyadic decomposition,
in any complete normed target space (in particular, spacetime `Lp`). -/
theorem logarithmic_dyadic_sum_bound {E : Type*} [NormedAddCommGroup E]
    [CompleteSpace E] (u : ℕ → E) {A B C : ℝ} (hB : A + 1 < B)
    (hu : ∀ j : ℕ, ‖u j‖ ≤ C * (1 + (j : ℝ)) ^ (A - B)) :
    Summable u ∧ ‖∑' j, u j‖ ≤ C * ∑' j : ℕ, (1 + (j : ℝ)) ^ (A - B) := by
  have hs := ((logarithmic_dyadic_summable_iff A B).mpr hB).mul_left C
  have hs' := hs.of_norm_bounded hu
  refine ⟨hs', ?_⟩
  simpa only [tsum_mul_left] using hs'.hasSum.norm_le_of_bounded hs.hasSum hu

/-- The positive-loss summation step for a dyadic decomposition. -/
theorem positive_loss_dyadic_sum_bound {E : Type*} [NormedAddCommGroup E]
    [CompleteSpace E] (u : ℕ → E) (k : ℕ) {ε C : ℝ} (hε : 0 < ε)
    (hu : ∀ j : ℕ, ‖u j‖ ≤ C * ((2 : ℝ) ^ (-(j : ℝ) * ε) * (1 + (j : ℝ)) ^ k)) :
    Summable u ∧ ‖∑' j, u j‖ ≤
      C * ∑' j : ℕ, (2 : ℝ) ^ (-(j : ℝ) * ε) * (1 + (j : ℝ)) ^ k := by
  have hs := (positive_loss_dyadic_summable k hε).mul_left C
  have hs' := hs.of_norm_bounded hu
  refine ⟨hs', ?_⟩
  simpa only [tsum_mul_left] using hs'.hasSum.norm_le_of_bounded hs.hasSum hu

/-- The quantitative absence of stationary points away from the cone:
the phase gradient is `X - T • v`, where `v` is a unit frequency vector.
This is the lower bound used by the off-cone integration-by-parts argument. -/
theorem off_cone_phase_gradient_lower_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (X v : E) {T : ℝ} (hv : ‖v‖ = 1)
    (hT₀ : 0 ≤ T) (hT₁ : T ≤ 2) (hX : 3 ≤ ‖X‖) :
    ‖X‖ / 3 ≤ ‖X - T • v‖ := by
  have h := norm_sub_norm_le X (T • v)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hT₀, hv, mul_one] at h
  linarith

/-- Exact exponent arithmetic in the conversion from the sector estimate to
the periodic critical estimate. -/
theorem sector_logarithmic_exponent (n : ℝ) :
    3 * (n + 3) / 2 + (n - 1) / 2 + 1 = 2 * n + 5 := by ring

/-- The interpolation power appearing between the critical and `L∞` bounds. -/
theorem interpolated_exponent {n p : ℝ} (hn : n ≠ 1) (hp : p ≠ 0) :
    (n - 1) / 2 * (1 - (2 * n / (n - 1)) / p) = (n - 1) / 2 - n / p := by
  field_simp

end OAI.Analysis.Fourier.WavePackets
