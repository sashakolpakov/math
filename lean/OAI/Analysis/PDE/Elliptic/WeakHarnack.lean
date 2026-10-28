import OAI.Analysis.PDE.Elliptic.GeometricTail
import OAI.Analysis.PDE.Elliptic.TailMoment

open Set BoxIntegral _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The normalized weak Harnack estimate for a nonnegative uniformly
elliptic supersolution, proved through ABP growth and dyadic covering. -/
theorem uniform_normalized_weak_harnack {lam L : ℝ} (hlam : 0 < lam) (hL : 0 < L) :
    ∃ p C : ℝ, 0 < p ∧ 0 < C ∧
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
      ∫⁻ x in euclideanBox B, ENNReal.ofReal (u x) ^ p ≤
        ENNReal.ofReal C * volume (euclideanBox B) := by
  obtain ⟨M, theta, hM, htheta, htheta1, htail⟩ :=
    uniform_superlevel_geometric_tail (ι := ι) hlam hL
  obtain ⟨p, C, hp, hC, hm⟩ := geometric_tail_moment
    (X := EuclideanSpace ℝ ι) hM htheta htheta1
  refine ⟨p, C, hp, hC, ?_⟩
  intro B R hR hB A u hu hnonneg hlo hhi hLu hpoint
  have h := hm (volume.restrict (euclideanBox B)) u hu.continuous.measurable (fun k ↦ by
    rw [Measure.restrict_apply (measurableSet_lt measurable_const hu.continuous.measurable),
      Measure.restrict_apply_univ]
    exact htail B R hR hB A u hu hnonneg hlo hhi hLu hpoint k)
  simpa only [Measure.restrict_apply_univ] using h

end OAI.Analysis.PDE.Elliptic
