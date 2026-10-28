import OAI.Analysis.PDE.Elliptic.EuclideanCover

open Set BoxIntegral _root_.MeasureTheory _root_.MeasureTheory.Measure
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
theorem real_volume_euclideanBox (B : Box ι) {r : ℝ}
    (hwidth : ∀ i, B.upper i - B.lower i = 2 * r) :
    volume.real (euclideanBox B) = (2 * r) ^ Fintype.card ι := by
  simp only [measureReal_def, volume_euclideanBox, Box.volume_apply', hwidth,
    Finset.prod_const, Finset.card_univ]

omit [Nonempty ι] in
theorem exists_cube_measure_fraction {delta : ℝ} (hd : 0 < delta) :
    ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧ ∀ (B : Box ι) (r : ℝ), 0 < r →
      (∀ i, B.upper i - B.lower i = 2 * r) →
      eta * volume.real (euclideanBox B) ≤
        delta * volume.real (Metric.ball (cubeCenter B) r) := by
  let omega : ℝ := volume.real (Metric.ball (0 : EuclideanSpace ℝ ι) 1)
  have hw : 0 < omega := ENNReal.toReal_pos
    (ne_of_gt (Metric.measure_ball_pos volume _ (by norm_num))) measure_ball_lt_top.ne
  let c : ℝ := (2 : ℝ) ^ Fintype.card ι
  have hc : 0 < c := by dsimp [c]; positivity
  let eta : ℝ := min (1 / 2) (delta * omega / c)
  have he : 0 < eta := lt_min (by norm_num) (div_pos (mul_pos hd hw) hc)
  refine ⟨eta, he, (min_le_left _ _).trans_lt (by norm_num), ?_⟩
  intro B r hr hwidth
  have hcoef : eta * c ≤ delta * omega :=
    (le_div_iff₀ hc).mp (min_le_right _ _)
  have hball : volume.real (Metric.ball (cubeCenter B) r) =
      r ^ Fintype.card ι * omega := by
    have h := congrArg ENNReal.toReal (addHaar_ball_of_pos volume (cubeCenter B) hr)
    simpa only [measureReal_def, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg hr.le _), finrank_euclideanSpace, omega] using h
  rw [real_volume_euclideanBox B hwidth, hball]
  calc
    eta * (2 * r) ^ Fintype.card ι = (eta * c) * r ^ Fintype.card ι := by
      dsimp [c]
      rw [mul_pow]
      ring
    _ ≤ (delta * omega) * r ^ Fintype.card ι :=
      mul_le_mul_of_nonneg_right hcoef (pow_nonneg hr.le _)
    _ = delta * (r ^ Fintype.card ι * omega) := by ring

end OAI.Analysis.PDE.Elliptic
