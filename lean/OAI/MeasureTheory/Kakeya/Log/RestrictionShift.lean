import OAI.MeasureTheory.Kakeya.Log.RestrictionWindow

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal RealInnerProductSpace

noncomputable section
namespace OAI.MeasureTheory.Kakeya

/-- A uniformly bounded radial window with variation on scale `T` preserves
the quadratic far-field error. All constants are independent of `T`, the
kernel, the source location, and the direction. -/
theorem windowed_farField_kernel_expansion {n : ℕ} (β A B C W J : ℝ)
    (hC : 0 ≤ C) (hW : 0 ≤ W) (hJ : 0 ≤ J) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (T : ℝ), 0 < T →
      ∀ (K : Space n → ℂ) (w : ℝ → ℝ),
      (∀ r, |w r| ≤ W) →
      (∀ r t, |w r - w t| ≤ J * |r - t| / T) →
      (∀ x : Space n, 1 ≤ ‖x‖ →
        ‖((T * ‖x‖ ^ β : ℝ) : ℂ) * K x -
          (w ‖x‖ : ℂ) * (OAI.Analysis.Fourier.Restriction.radialOscillation A B ‖x‖ : ℝ)‖ ≤ C / ‖x‖) →
      ∀ (ω y : Space n) (t : ℝ), ‖ω‖ = 1 → 2 ≤ t → T ≤ t →
      ‖y‖ ≤ t / 2 →
      ‖((T * t ^ β : ℝ) : ℂ) * K (t • ω - y) -
        (w t : ℂ) * (OAI.Analysis.Fourier.Restriction.radialOscillation A B (t - inner ℝ ω y) : ℝ)‖ ≤
        D * (1 + ‖y‖ ^ 2) / T := by
  obtain ⟨L, hL, hLip⟩ := OAI.Analysis.Fourier.Restriction.exists_rpow_local_lipschitz (-β)
  let H := |A| + |B|
  have hH : 0 ≤ H := add_nonneg (abs_nonneg _) (abs_nonneg _)
  let D := 2 * (L + 1) * C + L * W * H + J * H + W * H
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro T hT K w hwb hwl hK ω y t hω ht hTt hy
  have ht0 : 0 < t := by linarith
  let r := ‖t • ω - y‖
  let b := t - inner ℝ ω y
  have hr := OAI.Analysis.Fourier.Restriction.farField_norm_comparable hω ht0 hy
  have hr0 : 0 < r := by dsimp [r]; linarith [hr.1]
  have hr1 : 1 ≤ r := by dsimp [r]; linarith [hr.1]
  have hrs : r / t ∈ Icc (1 / 2 : ℝ) (3 / 2) := by
    constructor
    · apply (le_div_iff₀ ht0).mpr
      dsimp [r]; linarith [hr.1]
    · apply (div_le_iff₀ ht0).mpr
      dsimp [r]; linarith [hr.2]
  let q := (r / t) ^ (-β)
  have hq1 : |q - 1| ≤ L * (‖y‖ / T) := by
    calc
      _ ≤ L * (‖y‖ / t) :=
        (hLip _ hrs).1.trans (mul_le_mul_of_nonneg_left (OAI.Analysis.Fourier.Restriction.farField_norm_ratio hω ht0) hL)
      _ ≤ _ := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (norm_nonneg _) hT hTt) hL
  have hq : |q| ≤ L + 1 := by simpa only [add_comm] using (hLip _ hrs).2
  have hqr : q * r ^ β = t ^ β := by
    dsimp [q]
    rw [Real.rpow_neg (div_nonneg hr0.le ht0.le), Real.div_rpow hr0.le ht0.le, inv_div]
    exact div_mul_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos hr0 _))
  have he : ((T * t ^ β : ℝ) : ℂ) * K (t • ω - y) -
      (w t : ℂ) * (OAI.Analysis.Fourier.Restriction.radialOscillation A B b : ℝ) =
      (q : ℂ) * (((T * r ^ β : ℝ) : ℂ) * K (t • ω - y) -
        (w r : ℂ) * (OAI.Analysis.Fourier.Restriction.radialOscillation A B r : ℝ)) +
      ((q - 1 : ℝ) : ℂ) * (w r : ℂ) * (OAI.Analysis.Fourier.Restriction.radialOscillation A B r : ℝ) +
      ((w r - w t : ℝ) : ℂ) * (OAI.Analysis.Fourier.Restriction.radialOscillation A B r : ℝ) +
      (w t : ℂ) * ((OAI.Analysis.Fourier.Restriction.radialOscillation A B r - OAI.Analysis.Fourier.Restriction.radialOscillation A B b : ℝ) : ℂ) := by
    rw [← hqr]
    push_cast
    ring
  have hphase : |OAI.Analysis.Fourier.Restriction.radialOscillation A B r - OAI.Analysis.Fourier.Restriction.radialOscillation A B b| ≤ H * (‖y‖ ^ 2 / T) := by
    calc
      _ ≤ H * (‖y‖ ^ 2 / t) := by
        apply (OAI.Analysis.Fourier.Restriction.radialOscillation_lipschitz A B r b).trans
        apply mul_le_mul_of_nonneg_left _ hH
        rw [show r - b = ‖t • ω - y‖ - t + inner ℝ ω y by dsimp [r, b]; ring]
        exact OAI.Analysis.Fourier.Restriction.farField_distance_error hω ht0 hy
      _ ≤ _ := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (sq_nonneg _) hT hTt) hH
  have hdist : |r - t| ≤ ‖y‖ := by
    have htω : ‖t • ω‖ = t := by simp [norm_smul, hω, abs_of_pos ht0]
    have H₁ := norm_sub_norm_le (t • ω) y
    have H₂ := norm_sub_le (t • ω) y
    rw [htω] at H₁ H₂
    apply abs_le.mpr
    dsimp [r]
    constructor <;> linarith
  have hwindow : |w r - w t| ≤ J * ‖y‖ / T :=
    (hwl r t).trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdist hJ) hT.le)
  have hrem : C / r ≤ 2 * C / T := by
    have hrt : C / r ≤ 2 * C / t := by
      apply (div_le_div_iff₀ hr0 ht0).mpr
      have H' := mul_le_mul_of_nonneg_left hr.1 (show 0 ≤ 2 * C by positivity)
      dsimp [r]
      nlinarith
    exact hrt.trans (div_le_div_of_nonneg_left (by positivity) hT hTt)
  calc
    _ ≤ |q| * ‖((T * r ^ β : ℝ) : ℂ) * K (t • ω - y) -
          (w r : ℂ) * (OAI.Analysis.Fourier.Restriction.radialOscillation A B r : ℝ)‖ +
        |q - 1| * |w r| * |OAI.Analysis.Fourier.Restriction.radialOscillation A B r| +
        |w r - w t| * |OAI.Analysis.Fourier.Restriction.radialOscillation A B r| +
        |w t| * |OAI.Analysis.Fourier.Restriction.radialOscillation A B r - OAI.Analysis.Fourier.Restriction.radialOscillation A B b| := by
      rw [he]
      calc
        _ ≤ ‖(q : ℂ) * (((T * r ^ β : ℝ) : ℂ) * K (t • ω - y) -
              (w r : ℂ) * (OAI.Analysis.Fourier.Restriction.radialOscillation A B r : ℝ))‖ +
            ‖((q - 1 : ℝ) : ℂ) * (w r : ℂ) * (OAI.Analysis.Fourier.Restriction.radialOscillation A B r : ℝ)‖ +
            ‖((w r - w t : ℝ) : ℂ) * (OAI.Analysis.Fourier.Restriction.radialOscillation A B r : ℝ)‖ +
            ‖(w t : ℂ) * ((OAI.Analysis.Fourier.Restriction.radialOscillation A B r - OAI.Analysis.Fourier.Restriction.radialOscillation A B b : ℝ) : ℂ)‖ :=
          (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
            (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
        _ = _ := by simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (L + 1) * (2 * C / T) + (L * (‖y‖ / T)) * W * H +
        (J * ‖y‖ / T) * H + W * (H * (‖y‖ ^ 2 / T)) := by
      gcongr
      · exact (hK _ hr1).trans hrem
      · exact hwb r
      · exact OAI.Analysis.Fourier.Restriction.abs_radialOscillation_le A B r
      · exact OAI.Analysis.Fourier.Restriction.abs_radialOscillation_le A B r
      · exact hwb t
    _ = (2 * (L + 1) * C + (L * W * H + J * H) * ‖y‖ + W * H * ‖y‖ ^ 2) / T := by ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ hT.le
      have hy' : ‖y‖ ≤ 1 + ‖y‖ ^ 2 := by nlinarith [sq_nonneg (‖y‖ - 1 / 2)]
      have h₁ := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 1 + ‖y‖ ^ 2 by nlinarith [sq_nonneg ‖y‖])
        (show 0 ≤ 2 * (L + 1) * C by positivity)
      have h₂ := mul_le_mul_of_nonneg_left hy' (show 0 ≤ L * W * H + J * H by positivity)
      have h₃ := mul_le_mul_of_nonneg_left (show ‖y‖ ^ 2 ≤ 1 + ‖y‖ ^ 2 by linarith) (mul_nonneg hW hH)
      dsimp [D]
      nlinarith

end OAI.MeasureTheory.Kakeya
