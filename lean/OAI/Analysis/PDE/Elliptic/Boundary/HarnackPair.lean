import OAI.Analysis.PDE.Elliptic.HarnackSource
import OAI.Analysis.PDE.Elliptic.Evans.MomentPoint

/-! A quantitative two-function alternative for boundary slope iteration,
deduced from the proved weak Harnack estimate, not assumed Harnack data. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set BoxIntegral _root_.MeasureTheory
open scoped ENNReal

theorem weak_harnack_pair_lower
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {lam L : ℝ} (hlam : 0 < lam) (hL : 0 < L) :
    ∃ c : ℝ, 0 < c ∧ ∀ (B : Box ι) (R K s : ℝ), 0 < R → 0 ≤ K →
      (∀ i, B.upper i - B.lower i = 2 * R) →
      ∀ (A : Fin 2 → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
        (v : Fin 2 → EuclideanSpace ℝ ι → ℝ),
      (∀ j, ContDiff ℝ 2 (v j)) →
      (∀ j, ∀ x ∈ Metric.closedBall (cubeCenter B) (8 * (Fintype.card ι : ℝ) * R), 0 ≤ v j x) →
      (∀ j, ∀ x ∈ Metric.closedBall (cubeCenter B) (8 * (Fintype.card ι : ℝ) * R), ∀ w,
        lam * ‖w‖ ^ 2 ≤ inner ℝ w (A j x w)) →
      (∀ j, ∀ x ∈ Metric.closedBall (cubeCenter B) (8 * (Fintype.card ι : ℝ) * R), ∀ w,
        inner ℝ w (A j x w) ≤ L * ‖w‖ ^ 2) →
      (∀ j, ∀ x ∈ Metric.ball (cubeCenter B) (8 * (Fintype.card ι : ℝ) * R),
        ellipticTrace (A j) (v j) x ≤ 2 * K * lam * Fintype.card ι) →
      (∀ x ∈ euclideanBox B, s ≤ v 0 x + v 1 x) →
      ∃ j : Fin 2, ∀ x ∈ euclideanBox B,
        c * s - K * (8 * (Fintype.card ι : ℝ) * R) ^ 2 ≤ v j x := by
  classical
  obtain ⟨p, H, hp, hH, hh⟩ := uniform_weak_harnack_bounded_source (ι := ι) hlam hL
  obtain ⟨J, hJ, hj⟩ := finite_rpow_moments_common_point
    (X := EuclideanSpace ℝ ι) (I := Fin 2) hp hH
  let c := 1 / (4 * J)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  intro B R K s hR hK hB A v hv hnonneg hlo hhi hLu hsum
  let D := 8 * (Fintype.card ι : ℝ) * R
  let t := c * s - K * D ^ 2
  have hQ : euclideanBox B ⊆ Metric.closedBall (cubeCenter B) D := by
    apply (euclideanBox_subset_closedBall B hR.le hB).trans
    apply Metric.closedBall_subset_closedBall
    dsimp [D]
    nlinarith [mul_nonneg (Nat.cast_nonneg (Fintype.card ι) : (0 : ℝ) ≤ _) hR.le]
  by_cases ht : t ≤ 0
  · exact ⟨0, fun x hx => ht.trans (hnonneg 0 x (hQ hx))⟩
  have htpos : 0 < t := lt_of_not_ge ht
  have hcs : 0 < c * s := by
    have he : 0 ≤ K * D ^ 2 := mul_nonneg hK (sq_nonneg _)
    dsimp only [t] at htpos
    linarith
  have hs : 0 < s := (mul_pos_iff_of_pos_left hc).mp hcs
  by_contra! hn
  have hQ0 : volume (euclideanBox B) ≠ 0 := ne_of_gt
    ((Metric.measure_ball_pos volume (cubeCenter B) hR).trans_le
      (measure_mono (ball_subset_euclideanBox B hB)))
  have hQfin : volume (euclideanBox B) ≠ ∞ := ne_of_lt
    ((measure_mono hQ).trans_lt measure_closedBall_lt_top)
  have hmoment (j : Fin 2) : (∫⁻ x in euclideanBox B, ENNReal.ofReal (v j x) ^ p) ≤
      ENNReal.ofReal (H * (c * s) ^ p) * volume (euclideanBox B) := by
    obtain ⟨x, hx, hvx⟩ := hn j
    have h := hh B R t K hR htpos hK hB (A j) (v j) (hv j)
      (hnonneg j) (hlo j) (hhi j) (hLu j) ⟨x, hx, hvx.le⟩
    have he : t + K * (8 * (Fintype.card ι : ℝ) * R) ^ 2 = c * s := by dsimp [t, D]; ring
    simpa only [he] using h
  obtain ⟨x, hx, hpoint⟩ := hj volume (euclideanBox B) (measurableSet_euclideanBox B)
    hQ0 hQfin (c * s) hcs v (fun j => (hv j).continuous.measurable)
    (fun j x hx => hnonneg j x (hQ hx)) hmoment
  have hzero := hpoint 0
  have hone := hpoint 1
  have he : J * (c * s) = s / 4 := by dsimp [c]; field_simp
  rw [he] at hzero hone
  linarith [hsum x hx]

end OAI.Analysis.PDE.Elliptic
