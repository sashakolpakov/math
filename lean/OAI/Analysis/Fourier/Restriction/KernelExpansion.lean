import OAI.Analysis.Fourier.Restriction.RadialModel

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal RealInnerProductSpace
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

/-- A radial asymptotic yields the uniform linear-phase expansion needed for
restriction, with a quadratic error in the source location. -/
theorem farField_kernel_expansion {n : ℕ} (K : Space n → ℂ) (β A B C : ℝ)
    (hC : 0 ≤ C)
    (hK : ∀ x : Space n, 1 ≤ ‖x‖ →
      ‖(‖x‖ ^ β : ℝ) * K x - (radialOscillation A B ‖x‖ : ℝ)‖ ≤ C / ‖x‖) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (ω y : Space n) (t : ℝ), ‖ω‖ = 1 → 2 ≤ t →
      ‖y‖ ≤ t / 2 →
      ‖(t ^ β : ℝ) * K (t • ω - y) -
        (radialOscillation A B (t - inner ℝ ω y) : ℝ)‖ ≤
          D * (1 + ‖y‖ ^ 2) / t := by
  obtain ⟨L, hL, hLip⟩ := exists_rpow_local_lipschitz (-β)
  let H := |A| + |B|
  have hH : 0 ≤ H := add_nonneg (abs_nonneg _) (abs_nonneg _)
  refine ⟨2 * (L + 1) * C + (L + 1) * H, by positivity, ?_⟩
  intro ω y t hω ht hy
  have ht0 : 0 < t := by linarith
  let r := ‖t • ω - y‖
  let b := t - inner ℝ ω y
  have hr := farField_norm_comparable hω ht0 hy
  have hr0 : 0 < r := by dsimp [r]; linarith [hr.1]
  have hr1 : 1 ≤ r := by dsimp [r]; linarith [hr.1]
  have hrs : r / t ∈ Icc (1 / 2 : ℝ) (3 / 2) := by
    constructor
    · apply (le_div_iff₀ ht0).mpr
      dsimp [r]; linarith [hr.1]
    · apply (div_le_iff₀ ht0).mpr
      dsimp [r]; linarith [hr.2]
  let q := (r / t) ^ (-β)
  have hq0 : 0 ≤ q := Real.rpow_nonneg (div_nonneg hr0.le ht0.le) _
  have hq1 : |q - 1| ≤ L * (‖y‖ / t) :=
    (hLip _ hrs).1.trans (mul_le_mul_of_nonneg_left (farField_norm_ratio hω ht0) hL)
  have hq : |q| ≤ L + 1 := by simpa only [add_comm] using (hLip _ hrs).2
  have hqr : q * r ^ β = t ^ β := by
    dsimp [q]
    rw [Real.rpow_neg (div_nonneg hr0.le ht0.le), Real.div_rpow hr0.le ht0.le, inv_div]
    exact div_mul_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos hr0 _))
  have he : ((t ^ β : ℝ) : ℂ) * K (t • ω - y) - (radialOscillation A B b : ℝ) =
      (q : ℂ) * ((r ^ β : ℝ) * K (t • ω - y) - (radialOscillation A B r : ℝ)) +
      ((q - 1 : ℝ) : ℂ) * (radialOscillation A B r : ℝ) +
      ((radialOscillation A B r - radialOscillation A B b : ℝ) : ℂ) := by
    rw [← hqr]
    push_cast
    ring
  have hphase : |radialOscillation A B r - radialOscillation A B b| ≤ H * (‖y‖ ^ 2 / t) := by
    apply (radialOscillation_lipschitz A B r b).trans
    apply mul_le_mul_of_nonneg_left _ hH
    rw [show r - b = ‖t • ω - y‖ - t + inner ℝ ω y by dsimp [r, b]; ring]
    exact farField_distance_error hω ht0 hy
  have hrem : C / r ≤ 2 * C / t := by
    apply (div_le_div_iff₀ hr0 ht0).mpr
    have H' := mul_le_mul_of_nonneg_left hr.1 (show 0 ≤ 2 * C by positivity)
    dsimp [r]
    nlinarith
  calc
    _ ≤ |q| * ‖(r ^ β : ℝ) * K (t • ω - y) - (radialOscillation A B r : ℝ)‖ +
        |q - 1| * |radialOscillation A B r| +
        |radialOscillation A B r - radialOscillation A B b| := by
      rw [he]
      calc
        _ ≤ ‖(q : ℂ) * ((r ^ β : ℝ) * K (t • ω - y) - (radialOscillation A B r : ℝ))‖ +
            ‖((q - 1 : ℝ) : ℂ) * (radialOscillation A B r : ℝ)‖ +
            ‖((radialOscillation A B r - radialOscillation A B b : ℝ) : ℂ)‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ = _ := by simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (L + 1) * (2 * C / t) + (L * (‖y‖ / t)) * H + H * (‖y‖ ^ 2 / t) := by
      gcongr
      · exact (hK _ hr1).trans hrem
      · exact abs_radialOscillation_le A B r
    _ = (2 * (L + 1) * C + L * H * ‖y‖ + H * ‖y‖ ^ 2) / t := by ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ ht0.le
      have hy' : ‖y‖ ≤ 1 + ‖y‖ ^ 2 := by nlinarith [sq_nonneg (‖y‖ - 1 / 2)]
      have h1 := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 1 + ‖y‖ ^ 2 by nlinarith [sq_nonneg ‖y‖])
        (show 0 ≤ 2 * (L + 1) * C by positivity)
      have h2 := mul_le_mul_of_nonneg_left hy' (mul_nonneg hL hH)
      have h3 := mul_le_mul_of_nonneg_left (show ‖y‖ ^ 2 ≤ 1 + ‖y‖ ^ 2 by linarith) hH
      nlinarith

end OAI.Analysis.Fourier.Restriction
