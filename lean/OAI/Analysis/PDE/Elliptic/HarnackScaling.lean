import OAI.Analysis.PDE.Elliptic.WeakHarnack

open Set BoxIntegral _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

theorem lintegral_rpow_amplitude {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (u : X → ℝ) {t p : ℝ} (ht : 0 < t) (hp : 0 ≤ p) :
    (∫⁻ x, ENNReal.ofReal (u x) ^ p ∂mu) =
      ENNReal.ofReal t ^ p * ∫⁻ x, ENNReal.ofReal (t⁻¹ * u x) ^ p ∂mu := by
  rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp ENNReal.ofReal_ne_top)]
  apply lintegral_congr
  intro x
  have he : ENNReal.ofReal (u x) = ENNReal.ofReal t * ENNReal.ofReal (t⁻¹ * u x) := by
    rw [← ENNReal.ofReal_mul ht.le, ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]
  rw [he, ENNReal.mul_rpow_of_nonneg _ _ hp]

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The weak Harnack estimate at an arbitrary positive normalization. -/
theorem uniform_weak_harnack_at_level {lam L : ℝ} (hlam : 0 < lam) (hL : 0 < L) :
    ∃ p C : ℝ, 0 < p ∧ 0 < C ∧
      ∀ (B : Box ι) (R t : ℝ), 0 < R → 0 < t →
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
      (∃ x ∈ euclideanBox B, u x ≤ t) →
      ∫⁻ x in euclideanBox B, ENNReal.ofReal (u x) ^ p ≤
        ENNReal.ofReal (C * t ^ p) * volume (euclideanBox B) := by
  obtain ⟨p, C, hp, hC, hmain⟩ := uniform_normalized_weak_harnack (ι := ι) hlam hL
  refine ⟨p, C, hp, hC, ?_⟩
  intro B R t hR ht hB A u hu hnonneg hlo hhi hLu hpoint
  have hnonneg' : ∀ x ∈ Metric.closedBall (cubeCenter B) (8 * (Fintype.card ι : ℝ) * R),
      0 ≤ t⁻¹ • u x := fun x hx ↦ mul_nonneg (inv_nonneg.mpr ht.le) (hnonneg x hx)
  have hLu' : ∀ x ∈ Metric.ball (cubeCenter B) (8 * (Fintype.card ι : ℝ) * R),
      ellipticTrace A (fun y ↦ t⁻¹ • u y) x ≤ 0 := by
    intro x hx
    rw [ellipticTrace_smul A hu]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht.le) (hLu x hx)
  have hpoint' : ∃ x ∈ euclideanBox B, t⁻¹ • u x ≤ 1 := by
    obtain ⟨x, hx, hux⟩ := hpoint
    refine ⟨x, hx, ?_⟩
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using (div_le_one ht).mpr hux
  have hn := hmain B R hR hB A (fun y ↦ t⁻¹ • u y) (hu.const_smul t⁻¹)
    hnonneg' hlo hhi hLu' hpoint'
  calc
    (∫⁻ x in euclideanBox B, ENNReal.ofReal (u x) ^ p) = ENNReal.ofReal t ^ p *
        ∫⁻ x in euclideanBox B, ENNReal.ofReal (t⁻¹ * u x) ^ p :=
      lintegral_rpow_amplitude _ u ht hp.le
    _ ≤ ENNReal.ofReal t ^ p * (ENNReal.ofReal C * volume (euclideanBox B)) :=
      mul_le_mul_of_nonneg_left hn zero_le
    _ = ENNReal.ofReal (C * t ^ p) * volume (euclideanBox B) := by
      rw [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_rpow_of_pos ht]
      ac_rfl

end OAI.Analysis.PDE.Elliptic
