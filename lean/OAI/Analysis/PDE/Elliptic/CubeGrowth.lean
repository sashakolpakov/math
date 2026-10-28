import OAI.Analysis.PDE.Elliptic.CubeParents
import OAI.Analysis.PDE.Elliptic.CubeMeasure
import OAI.Analysis.PDE.Elliptic.LevelMeasure

open Set BoxIntegral _root_.MeasureTheory
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- A high-density superlevel set in a cube forces a lower bound on
a surrounding ball, large enough to contain the dyadic parent. -/
theorem cube_superlevel_ball {lam L : ℝ} (hlam : 0 < lam) (hL : 0 < L) :
    ∃ M eta : ℝ, 1 < M ∧ 0 < eta ∧ eta < 1 ∧
      ∀ (B : Box ι) (r t : ℝ), 0 < r → 0 < t →
      (∀ i, B.upper i - B.lower i = 2 * r) →
      ∀ (A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
        (u : EuclideanSpace ℝ ι → ℝ), ContDiff ℝ 2 u →
      (∀ x ∈ Metric.closedBall (cubeCenter B)
        (2 * (3 * (Fintype.card ι : ℝ)) * r), 0 ≤ u x) →
      (∀ x ∈ Metric.closedBall (cubeCenter B)
        (2 * (3 * (Fintype.card ι : ℝ)) * r), ∀ v,
        lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)) →
      (∀ x ∈ Metric.closedBall (cubeCenter B)
        (2 * (3 * (Fintype.card ι : ℝ)) * r), ∀ v,
        inner ℝ v (A x v) ≤ L * ‖v‖ ^ 2) →
      (∀ x ∈ Metric.ball (cubeCenter B)
        (2 * (3 * (Fintype.card ι : ℝ)) * r), ellipticTrace A u x ≤ 0) →
      (1 - eta) * volume.real (euclideanBox B) <
        volume.real (euclideanBox B ∩ {x | t * M < u x}) →
      ∀ x ∈ Metric.closedBall (cubeCenter B) (3 * (Fintype.card ι : ℝ) * r), t < u x := by
  have hd : (1 : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Fintype.card_ne_zero (α := ι)))
  have hR : 1 ≤ 3 * (Fintype.card ι : ℝ) := by linarith
  obtain ⟨M, delta, hM, hdelta, _, hg⟩ := small_sublevel_forces_lower_bound
    (volume : Measure (EuclideanSpace ℝ ι)) hlam hL hR
  obtain ⟨eta, heta, heta1, he⟩ := exists_cube_measure_fraction (ι := ι) hdelta
  refine ⟨M, eta, hM, heta, heta1, ?_⟩
  intro B r t hr ht hwidth A u hu hnonneg hlo hhi hLu hhigh
  let C := B
  have hCwidth : ∀ i, C.upper i - C.lower i = 2 * r := hwidth
  have hCfinite : volume (euclideanBox C) ≠ ⊤ := by
    rw [volume_euclideanBox]
    exact (C.measure_coe_lt_top volume).ne
  have hsmall := sublevel_lt_of_superlevel_gt volume (measurableSet_euclideanBox C) hCfinite
    (ball_subset_euclideanBox C hCwidth) hu.continuous.measurable hhigh
  have hsmall' : volume.real {x : EuclideanSpace ℝ ι |
      dist x (cubeCenter C) < r ∧ u x ≤ t * M} <
      delta * volume.real (Metric.ball (cubeCenter C) r) :=
    hsmall.trans_le (he C r hr hCwidth)
  exact hg (cubeCenter C) r t hr ht A u hu hnonneg hlo hhi hLu hsmall'

end OAI.Analysis.PDE.Elliptic
