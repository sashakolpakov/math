import OAI.Analysis.PDE.Schauder.Calculus.Boundary.SchauderZero

/-! Absorption of a small Hölder error without assuming an attained seminorm. -/

noncomputable section
open Set Filter
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

theorem geometric_holder_absorption {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    (f : E → F) (s : Set E) (α M H₀ : ℝ) (hM : 0 ≤ M) (hH₀ : 0 ≤ H₀)
    (h₀ : ∀ x ∈ s, ∀ y ∈ s, ‖f x - f y‖ ≤ H₀ * ‖x - y‖ ^ α)
    (hstep : ∀ H, 0 ≤ H →
      (∀ x ∈ s, ∀ y ∈ s, ‖f x - f y‖ ≤ H * ‖x - y‖ ^ α) →
      ∀ x ∈ s, ∀ y ∈ s, ‖f x - f y‖ ≤ (M + H / 2) * ‖x - y‖ ^ α) :
    ∀ x ∈ s, ∀ y ∈ s, ‖f x - f y‖ ≤ (2 * M) * ‖x - y‖ ^ α := by
  have hn (n : ℕ) : ∀ x ∈ s, ∀ y ∈ s,
      ‖f x - f y‖ ≤ (2 * M + (1 / 2 : ℝ) ^ n * H₀) * ‖x - y‖ ^ α := by
    induction n with
    | zero =>
      intro x hx y hy
      apply (h₀ x hx y hy).trans
      exact mul_le_mul_of_nonneg_right (by norm_num; linarith) (Real.rpow_nonneg (norm_nonneg _) _)
    | succ n ih =>
      have hh := hstep (2 * M + (1 / 2 : ℝ) ^ n * H₀) (by positivity) ih
      have he : M + (2 * M + (1 / 2 : ℝ) ^ n * H₀) / 2 =
          2 * M + (1 / 2 : ℝ) ^ (n + 1) * H₀ := by rw [pow_succ]; ring
      simpa only [he] using hh
  intro x hx y hy
  have ht : Tendsto (fun n : ℕ => (2 * M + (1 / 2 : ℝ) ^ n * H₀) * ‖x - y‖ ^ α)
      atTop (𝓝 ((2 * M) * ‖x - y‖ ^ α)) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) < 1 by norm_num)
    simpa using (tendsto_const_nhds.add (hp.mul_const H₀)).mul_const (‖x - y‖ ^ α)
  exact ge_of_tendsto ht (Filter.Eventually.of_forall fun n => hn n x hx y hy)

end OAI.Analysis.PDE.Schauder
