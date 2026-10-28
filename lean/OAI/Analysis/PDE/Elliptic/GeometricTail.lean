import OAI.Analysis.PDE.Elliptic.MeasureDecay

open Set BoxIntegral _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Geometric superlevel decay with constants depending only on the
dimension and ellipticity bounds. -/
theorem uniform_superlevel_geometric_tail {lam L : ℝ} (hlam : 0 < lam) (hL : 0 < L) :
    ∃ M theta : ℝ, 1 < M ∧ 0 < theta ∧ theta < 1 ∧
      ∀ (B : Box ι) (R : ℝ), 0 < R →
      (∀ i, B.upper i - B.lower i = 2 * R) →
      ∀ (A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
        (u : EuclideanSpace ℝ ι → ℝ), ContDiff ℝ 2 u →
      (∀ x ∈ Metric.closedBall (cubeCenter B) (8 * (Fintype.card ι : ℝ) * R), 0 ≤ u x) →
      (∀ x ∈ Metric.closedBall (cubeCenter B) (8 * (Fintype.card ι : ℝ) * R), ∀ v,
        lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)) →
      (∀ x ∈ Metric.closedBall (cubeCenter B) (8 * (Fintype.card ι : ℝ) * R), ∀ v,
        inner ℝ v (A x v) ≤ L * ‖v‖ ^ 2) →
      (∀ x ∈ Metric.ball (cubeCenter B) (8 * (Fintype.card ι : ℝ) * R),
        ellipticTrace A u x ≤ 0) →
      (∃ x ∈ euclideanBox B, u x ≤ 1) →
      ∀ k : ℕ, volume ({x | M ^ k < u x} ∩ euclideanBox B) ≤
        ENNReal.ofReal theta ^ k * volume (euclideanBox B) := by
  obtain ⟨M, theta, hM, htheta, htheta1, hdecay⟩ :=
    uniform_superlevel_measure_decay (ι := ι) hlam hL
  refine ⟨M, theta, hM, htheta, htheta1, ?_⟩
  intro B R hR hB A u hu hnonneg hlo hhi hLu hpoint k
  induction k with
  | zero => simpa only [pow_zero, one_mul] using (measure_mono inter_subset_right :
      volume ({x | (1 : ℝ) < u x} ∩ euclideanBox B) ≤ volume (euclideanBox B))
  | succ k ih =>
      have hstep := hdecay B R hR hB A u hu hnonneg hlo hhi hLu hpoint
        (M ^ k) (one_le_pow₀ hM.le)
      calc
        volume ({x | M ^ (k + 1) < u x} ∩ euclideanBox B) ≤
            ENNReal.ofReal theta * volume ({x | M ^ k < u x} ∩ euclideanBox B) := by
          simpa only [pow_succ] using hstep
        _ ≤ ENNReal.ofReal theta * (ENNReal.ofReal theta ^ k * volume (euclideanBox B)) :=
          mul_le_mul_of_nonneg_left ih zero_le
        _ = ENNReal.ofReal theta ^ (k + 1) * volume (euclideanBox B) := by
          rw [pow_succ]
          ac_rfl

end OAI.Analysis.PDE.Elliptic
