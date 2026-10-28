import OAI.Analysis.PDE.Elliptic.HarnackScaling
import OAI.Analysis.PDE.Elliptic.Quadratic

open Set BoxIntegral _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Weak Harnack with bounded forcing, expressed using the coefficient
of the quadratic correction. Every nonnegative constant forcing bound
has this form since the dimension and lower ellipticity bound are positive. -/
theorem uniform_weak_harnack_bounded_source {lam L : ℝ} (hlam : 0 < lam) (hL : 0 < L) :
    ∃ p C : ℝ, 0 < p ∧ 0 < C ∧
      ∀ (B : Box ι) (R t K : ℝ), 0 < R → 0 < t → 0 ≤ K →
      (∀ i, B.upper i - B.lower i = 2 * R) →
      ∀ (A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
        (u : EuclideanSpace ℝ ι → ℝ), ContDiff ℝ 2 u →
      (∀ x ∈ Metric.closedBall (cubeCenter B) (8 * (Fintype.card ι : ℝ) * R), 0 ≤ u x) →
      (∀ x ∈ Metric.closedBall (cubeCenter B) (8 * (Fintype.card ι : ℝ) * R), ∀ v,
        lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)) →
      (∀ x ∈ Metric.closedBall (cubeCenter B) (8 * (Fintype.card ι : ℝ) * R), ∀ v,
        inner ℝ v (A x v) ≤ L * ‖v‖ ^ 2) →
      (∀ x ∈ Metric.ball (cubeCenter B) (8 * (Fintype.card ι : ℝ) * R),
        ellipticTrace A u x ≤ 2 * K * lam * Fintype.card ι) →
      (∃ x ∈ euclideanBox B, u x ≤ t) →
      ∫⁻ x in euclideanBox B, ENNReal.ofReal (u x) ^ p ≤
        ENNReal.ofReal (C * (t + K * (8 * (Fintype.card ι : ℝ) * R) ^ 2) ^ p) *
          volume (euclideanBox B) := by
  obtain ⟨p, C, hp, hC, hh⟩ := uniform_weak_harnack_at_level (ι := ι) hlam hL
  refine ⟨p, C, hp, hC, ?_⟩
  intro B R t K hR ht hK hB A u hu hnonneg hlo hhi hLu hpoint
  let D : ℝ := 8 * (Fintype.card ι : ℝ) * R
  let w := fun x ↦ u x + K • quadraticBarrier (cubeCenter B) D x
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hT : 0 < t + K * D ^ 2 := by nlinarith [mul_nonneg hK (sq_nonneg D)]
  have hQ : euclideanBox B ⊆ Metric.closedBall (cubeCenter B) D := by
    apply (euclideanBox_subset_closedBall B hR.le hB).trans
    apply Metric.closedBall_subset_closedBall
    dsimp [D]
    nlinarith [mul_nonneg (Nat.cast_nonneg (Fintype.card ι) : (0 : ℝ) ≤ _) hR.le]
  have hw : ContDiff ℝ 2 w :=
    hu.add (((quadraticBarrier_contDiff (cubeCenter B) D).of_le (by simp)).const_smul K)
  have hwn : ∀ x ∈ Metric.closedBall (cubeCenter B) D, 0 ≤ w x := by
    intro x hx
    exact add_nonneg (hnonneg x hx) (mul_nonneg hK (quadraticBarrier_nonneg hD hx))
  have hwL : ∀ x ∈ Metric.ball (cubeCenter B) D, ellipticTrace A w x ≤ 0 := by
    intro x hx
    apply ellipticTrace_quadratic_correction A hu (cubeCenter B) x D hK
      (hlo x (Metric.ball_subset_closedBall hx))
    simpa only [finrank_euclideanSpace] using hLu x hx
  have hwp : ∃ x ∈ euclideanBox B, w x ≤ t + K * D ^ 2 := by
    obtain ⟨x, hx, hux⟩ := hpoint
    refine ⟨x, hx, ?_⟩
    have hqb := mul_le_mul_of_nonneg_left (quadraticBarrier_le (cubeCenter B) x D) hK
    change u x + K * quadraticBarrier (cubeCenter B) D x ≤ _
    linarith
  have hbound := hh B R (t + K * D ^ 2) hR hT hB A w hw hwn hlo hhi hwL hwp
  apply le_trans (lintegral_mono_ae ?_) hbound
  filter_upwards [ae_restrict_mem (measurableSet_euclideanBox B)] with x hx
  apply ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) hp.le
  have hq := mul_nonneg hK (quadraticBarrier_nonneg hD (hQ hx))
  change u x ≤ u x + K * quadraticBarrier (cubeCenter B) D x
  linarith

end OAI.Analysis.PDE.Elliptic
