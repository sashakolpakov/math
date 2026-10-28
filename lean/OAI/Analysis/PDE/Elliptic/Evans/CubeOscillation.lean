import OAI.Analysis.PDE.Elliptic.Evans.OscillationMoment
import OAI.Analysis.PDE.Elliptic.Evans.DeficitComparison

open Set BoxIntegral _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {ι J : Type*} [Fintype ι] [Nonempty ι] [Fintype J] [Nonempty J]

/-- Oscillation contraction for a finite family of elliptic subsolutions
coupled by the positive-direction comparison. This uses the proved weak
Harnack inequality, including its bounded forcing correction. -/
theorem cube_oscillation_contraction {lam L δ C F : ℝ}
    (hlam : 0 < lam) (hL : 0 < L) (hδ : 0 < δ) (hC : 0 < C) (hF : 0 ≤ F) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      ∀ (B : Box ι) (R K : ℝ), 0 < R → 0 ≤ K →
      (∀ i, B.upper i - B.lower i = 2 * R) →
      ∀ (A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
        (w : J → EuclideanSpace ℝ ι → ℝ) (M m Msmall msmall : J → ℝ),
      (∀ j, ContDiff ℝ 2 (w j)) →
      (∀ x ∈ Metric.closedBall (cubeCenter B) (8 * (Fintype.card ι : ℝ) * R), ∀ z,
        lam * ‖z‖ ^ 2 ≤ inner ℝ z (A x z)) →
      (∀ x ∈ Metric.closedBall (cubeCenter B) (8 * (Fintype.card ι : ℝ) * R), ∀ z,
        inner ℝ z (A x z) ≤ L * ‖z‖ ^ 2) →
      (∀ j x, x ∈ Metric.closedBall (cubeCenter B) (8 * (Fintype.card ι : ℝ) * R) →
        m j ≤ w j x ∧ w j x ≤ M j) →
      (∀ j x, x ∈ Metric.ball (cubeCenter B) (8 * (Fintype.card ι : ℝ) * R) →
        -(2 * K * lam * Fintype.card ι) ≤ ellipticTrace A (w j) x) →
      (∀ j, m j ≤ msmall j ∧ msmall j ≤ Msmall j ∧ Msmall j ≤ M j) →
      (∀ j, ∃ x ∈ euclideanBox B, w j x = Msmall j) →
      (∀ j, ∃ x ∈ euclideanBox B, w j x = msmall j) →
      (∀ x ∈ euclideanBox B, ∀ y ∈ euclideanBox B,
        ∃ a : J → ℝ, (∀ j, δ ≤ a j ∧ a j ≤ C) ∧
          -(F * R) ≤ ∑ j, a j * (w j x - w j y)) →
      (∑ j, (Msmall j - msmall j)) ≤ θ * (∑ j, (M j - m j)) +
        (R + K * (8 * (Fintype.card ι : ℝ) * R) ^ 2) := by
  classical
  obtain ⟨p, H, hp, hH, hh⟩ := uniform_weak_harnack_bounded_source (ι := ι) hlam hL
  let N : ℝ := Fintype.card J
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card J)
  obtain ⟨θ, hθ, hθ1, hosc⟩ := oscillation_contraction_of_moments
    (X := EuclideanSpace ℝ ι) (I := J) hp hH hδ (mul_pos hN hC) (mul_nonneg hN.le hF)
  refine ⟨θ, hθ, hθ1, ?_⟩
  intro B R K hR hK hB A w M m Msmall msmall hw hlo hhi houter hsource hlevels hmax hmin hrel
  let r := R + K * (8 * (Fintype.card ι : ℝ) * R) ^ 2
  let d : J → ℝ := fun j ↦ M j - Msmall j
  let v : J → EuclideanSpace ℝ ι → ℝ := fun j x ↦ M j - w j x
  have hr : 0 < r := by dsimp [r]; positivity
  have hRr : R ≤ r := by dsimp [r]; nlinarith [mul_nonneg hK (sq_nonneg (8 * (Fintype.card ι : ℝ) * R))]
  have hd (j : J) : 0 ≤ d j := sub_nonneg.mpr (hlevels j).2.2
  have hQ : euclideanBox B ⊆ Metric.closedBall (cubeCenter B) (8 * (Fintype.card ι : ℝ) * R) := by
    apply (euclideanBox_subset_closedBall B hR.le hB).trans
    apply Metric.closedBall_subset_closedBall
    nlinarith [mul_nonneg (Nat.cast_nonneg (Fintype.card ι) : (0 : ℝ) ≤ _) hR.le]
  have hQ0 : volume (euclideanBox B) ≠ 0 := ne_of_gt
    ((Metric.measure_ball_pos volume (cubeCenter B) hR).trans_le
      (measure_mono (ball_subset_euclideanBox B hB)))
  have hQfin : volume (euclideanBox B) ≠ ∞ := ne_of_lt
    ((measure_mono hQ).trans_lt measure_closedBall_lt_top)
  have hv (j : J) : ContDiff ℝ 2 (v j) := contDiff_const.sub (hw j)
  have hvnonneg (j : J) (x) (hx : x ∈ euclideanBox B) : 0 ≤ v j x :=
    sub_nonneg.mpr (houter j x (hQ hx)).2
  have hmom (j : J) : (∫⁻ x in euclideanBox B, ENNReal.ofReal (v j x) ^ p) ≤
      ENNReal.ofReal (H * (d j + r) ^ p) * volume (euclideanBox B) := by
    have ht : 0 < d j + R := add_pos_of_nonneg_of_pos (hd j) hR
    have hpoint : ∃ x ∈ euclideanBox B, v j x ≤ d j + R := by
      obtain ⟨x, hx, hxw⟩ := hmax j
      refine ⟨x, hx, ?_⟩
      dsimp [v, d]
      rw [hxw]
      linarith
    have hs := hh B R (d j + R) K hR ht hK hB A (v j) (hv j)
      (fun x hx ↦ sub_nonneg.mpr (houter j x hx).2) hlo hhi (by
        intro x hx
        change ellipticTrace A (fun y ↦ M j - w j y) x ≤ _
        rw [ellipticTrace_const_sub A (hw j)]
        linarith [hsource j x hx]) hpoint
    simpa only [r, add_assoc] using hs
  have hcomp (y) (hy : y ∈ euclideanBox B) :
      δ * (∑ j, (Msmall j - msmall j)) ≤ (N * C) * (∑ j, v j y) + (N * F) * r := by
    have hk (j : J) : δ * (Msmall j - msmall j) ≤ C * (∑ i, v i y) + F * R := by
      obtain ⟨x, hx, hxw⟩ := hmin j
      obtain ⟨a, ha, har⟩ := hrel x hx y hy
      have hc := weighted_deficit_comparison a M (fun i ↦ w i x) (fun i ↦ w i y)
        hδ.le ha (fun i ↦ (houter i x (hQ hx)).2) (fun i ↦ (houter i y (hQ hy)).2) har j
      rw [hxw] at hc
      apply le_trans _ hc
      exact mul_le_mul_of_nonneg_left (by linarith [(hlevels j).2.2]) hδ.le
    calc
      _ = ∑ j, δ * (Msmall j - msmall j) := Finset.mul_sum _ _ _
      _ ≤ ∑ _j : J, (C * (∑ i, v i y) + F * R) := Finset.sum_le_sum (fun j _ ↦ hk j)
      _ = (N * C) * (∑ i, v i y) + (N * F) * R := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        dsimp [N]
        ring
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hRr (mul_nonneg hN.le hF))
  have hdiff : (∑ j, d j) ≤ (∑ j, (M j - m j)) - ∑ j, (Msmall j - msmall j) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro j _
    dsimp [d]
    linarith [(hlevels j).1]
  exact hosc volume (euclideanBox B) (measurableSet_euclideanBox B) hQ0 hQfin v d r
    (∑ j, (Msmall j - msmall j)) (∑ j, (M j - m j)) hr hd
    (fun j ↦ (hv j).continuous.measurable) hvnonneg hmom hcomp hdiff

end OAI.Analysis.PDE.Elliptic
