import OAI.Analysis.PDE.Elliptic.GrowthBalls

open Set _root_.MeasureTheory _root_.MeasureTheory.Measure
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- The growth lemma in the form used by the covering argument:
a sufficiently small low-value set forces a lower bound throughout
the larger neighboring ball. -/
theorem small_sublevel_forces_lower_bound (μ : Measure E) [IsAddHaarMeasure μ]
    {lam L : ℝ} (hlam : 0 < lam) (hL : 0 < L) {R : ℝ} (hR : 1 ≤ R) :
    ∃ M delta : ℝ, 1 < M ∧ 0 < delta ∧ delta < 1 ∧
      ∀ (z : E) (r t : ℝ), 0 < r → 0 < t →
      ∀ (A : E → E →L[ℝ] E) (u : E → ℝ), ContDiff ℝ 2 u →
      (∀ x ∈ Metric.closedBall z (2 * R * r), 0 ≤ u x) →
      (∀ x ∈ Metric.closedBall z (2 * R * r), ∀ v : E,
        lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)) →
      (∀ x ∈ Metric.closedBall z (2 * R * r), ∀ v : E,
        inner ℝ v (A x v) ≤ L * ‖v‖ ^ 2) →
      (∀ x ∈ Metric.ball z (2 * R * r), ellipticTrace A u x ≤ 0) →
      μ.real {x : E | dist x z < r ∧ u x ≤ t * M} < delta * μ.real (Metric.ball z r) →
      ∀ x ∈ Metric.closedBall z (R * r), t < u x := by
  obtain ⟨M, delta, hM, hd, hd1, hg⟩ := uniform_sublevel_growth_balls_large μ hlam hL hR
  refine ⟨M, delta, hM, hd, hd1, ?_⟩
  intro z r t hr ht A u hu hnonneg hlo hhi hLu hsmall x hx
  apply lt_of_not_ge
  intro hux
  exact (not_le_of_gt hsmall) (hg z r t hr ht A u hu hnonneg hlo hhi hLu x hx hux)

end OAI.Analysis.PDE.Elliptic
