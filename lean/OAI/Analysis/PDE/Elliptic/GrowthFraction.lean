import OAI.Analysis.PDE.Elliptic.Growth

open Set _root_.MeasureTheory _root_.MeasureTheory.Measure
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- Relative-measure formulation of the growth lemma. The positive
fraction and the level are uniform in the coefficients and solution. -/
theorem uniform_sublevel_growth_fraction_large (μ : Measure E) [IsAddHaarMeasure μ]
    {lam L : ℝ} (hlam : 0 < lam) (hL : 0 < L) {R : ℝ} (hR : 1 ≤ R) :
    ∃ M delta : ℝ, 1 < M ∧ 0 < delta ∧ delta < 1 ∧
      ∀ (A : E → E →L[ℝ] E) (u : E → ℝ), ContDiff ℝ 2 u →
      (∀ x ∈ Metric.closedBall (0 : E) (2 * R), 0 ≤ u x) →
      (∀ x ∈ Metric.closedBall (0 : E) (2 * R), ∀ v : E,
        lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)) →
      (∀ x ∈ Metric.closedBall (0 : E) (2 * R), ∀ v : E,
        inner ℝ v (A x v) ≤ L * ‖v‖ ^ 2) →
      (∀ x ∈ interior (Metric.closedBall (0 : E) (2 * R)), ellipticTrace A u x ≤ 0) →
      ∀ x₀ ∈ Metric.closedBall (0 : E) R, u x₀ ≤ 1 →
        delta * μ.real (Metric.ball (0 : E) 1) ≤ μ.real {x : E | ‖x‖ < 1 ∧ u x ≤ M} := by
  obtain ⟨M, C, hM, hC, hest⟩ := uniform_sublevel_growth_large μ hlam hL hR
  have hRpos : 0 < R := by linarith
  let q : ℝ := (1 / (4 * R) : ℝ) ^ Module.finrank ℝ E
  have hq : 0 < q := by dsimp [q]; positivity
  let delta : ℝ := min (1 / 2) (q / C)
  have hd : 0 < delta := lt_min (by norm_num) (div_pos hq hC)
  refine ⟨M, delta, hM, hd, (min_le_left _ _).trans_lt (by norm_num), ?_⟩
  intro A u hu hnonneg hlo hhi hLu x₀ hx₀ hux₀
  have h := hest A u hu hnonneg hlo hhi hLu x₀ hx₀ hux₀
  let S : Set E := {x | ‖x‖ < 1 ∧ u x ≤ M}
  have hSsub : S ⊆ Metric.ball (0 : E) 1 := by
    intro x hx
    simpa only [Metric.mem_ball, dist_zero_right] using hx.1
  have hSfinite : μ S ≠ ⊤ := ne_of_lt ((measure_mono hSsub).trans_lt measure_ball_lt_top)
  have hfinite : ENNReal.ofReal C * μ S ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSfinite
  have hr : μ.real (Metric.ball (0 : E) (1 / (4 * R))) ≤ C * μ.real S := by
    simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hC.le] using
      ENNReal.toReal_mono hfinite h
  have hscale : μ.real (Metric.ball (0 : E) (1 / (4 * R))) = q * μ.real (Metric.ball (0 : E) 1) := by
    have he := congrArg ENNReal.toReal (addHaar_ball_of_pos μ (0 : E)
      (by positivity : (0 : ℝ) < 1 / (4 * R)))
    simpa only [measureReal_def, q, ENNReal.toReal_mul, ENNReal.toReal_ofReal hq.le] using he
  rw [hscale] at hr
  calc
    delta * μ.real (Metric.ball (0 : E) 1) ≤ (q / C) * μ.real (Metric.ball (0 : E) 1) :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (measureReal_nonneg)
    _ ≤ μ.real S := by
      rw [div_mul_eq_mul_div]
      exact (div_le_iff₀ hC).mpr (by nlinarith only [hr])

theorem uniform_sublevel_growth_fraction (μ : Measure E) [IsAddHaarMeasure μ]
    {lam L : ℝ} (hlam : 0 < lam) (hL : 0 < L) :
    ∃ M delta : ℝ, 1 < M ∧ 0 < delta ∧ delta < 1 ∧
      ∀ (A : E → E →L[ℝ] E) (u : E → ℝ), ContDiff ℝ 2 u →
      (∀ x ∈ Metric.closedBall (0 : E) 2, 0 ≤ u x) →
      (∀ x ∈ Metric.closedBall (0 : E) 2, ∀ v : E,
        lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)) →
      (∀ x ∈ Metric.closedBall (0 : E) 2, ∀ v : E,
        inner ℝ v (A x v) ≤ L * ‖v‖ ^ 2) →
      (∀ x ∈ interior (Metric.closedBall (0 : E) 2), ellipticTrace A u x ≤ 0) →
      ∀ x₀ ∈ Metric.closedBall (0 : E) 1, u x₀ ≤ 1 →
        delta * μ.real (Metric.ball (0 : E) 1) ≤ μ.real {x : E | ‖x‖ < 1 ∧ u x ≤ M} := by
  simpa using uniform_sublevel_growth_fraction_large μ hlam hL (R := 1) le_rfl

end OAI.Analysis.PDE.Elliptic
