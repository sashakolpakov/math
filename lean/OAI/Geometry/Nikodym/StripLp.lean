import OAI.Geometry.Nikodym.StripMeasurability
import OAI.Geometry.Nikodym.DirectionChartLp

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped ENNReal
namespace OAI.Geometry.Nikodym


theorem stripInput_idempotent {d : ℕ} (V : ℝ) (f : Space (d+1) → ℂ) :
    stripInput d V (stripInput d V f) = stripInput d V f := by
  funext x
  by_cases hx : (projectiveJoin d).symm x ∈ stripBox d V <;> simp [stripInput,hx]

theorem stripPullback_stripInput {d : ℕ} (V : ℝ) (f : Space (d+1) → ℂ) :
    stripPullback d V (stripInput d V f) = stripPullback d V f := by
  simp only [stripPullback,stripInput_idempotent]

theorem eLpNorm_stripPullback_local {d : ℕ} {V : ℝ} (hV : 0 ≤ V)
    {f : Space (d+1) → ℂ} (hf : Measurable f) (p : ℝ≥0∞) :
    eLpNorm (stripPullback d V f) p volume ≤
      (ENNReal.ofReal (projectiveDistortion (1/2) (2+2*V)) ^ (d+1)) ^
        (1/p).toReal * eLpNorm (stripInput d V f) p volume := by
  simpa only [stripPullback_stripInput] using
    eLpNorm_stripPullback hV (measurable_stripInput V hf) p

theorem stripMaximal_local_bound_ennreal (hK : OAI.MeasureTheory.Kakeya.KakeyaMaximalConjecture)
    {d : ℕ} (hd : 1 ≤ d) {V ε : ℝ} (hV : 0 ≤ V) (hε : 0 < ε) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1/2 → stripDilation V*δ ≤ 1 →
      ∀ f : Space (d+1) → ℂ, Measurable f → MemLp f (d+1 : ℕ) volume →
        eLpNorm (stripMaximal δ V f) (d+1 : ℕ) (volume.restrict (closedBall 0 1)) ≤
          C * ENNReal.ofReal (δ^(-ε)) * eLpNorm (stripInput d V f) (d+1 : ℕ) volume := by
  obtain ⟨A,hA,hpoint⟩ := exists_stripMaximal_pointwise_bound d hV
  obtain ⟨K,hKpos,hKbound⟩ := hK (d+1) (by omega) ε hε
  let p : ℝ≥0∞ := (d+1 : ℕ)
  let Q : ℝ≥0∞ := directionChartFactor d 1 ^ (1/p).toReal
  let R : ℝ≥0∞ := (ENNReal.ofReal (projectiveDistortion (1/2) (2+2*V))^(d+1)) ^ (1/p).toReal
  let C : ℝ≥0∞ := ENNReal.ofReal A * Q * ENNReal.ofReal K *
    ENNReal.ofReal ((stripDilation V)^(-ε)) * R
  have hQ : Q < ⊤ := by dsimp [Q,directionChartFactor]; finiteness
  have hR : R < ⊤ := by dsimp [R]; finiteness
  have hC : C < ⊤ := by dsimp [C]; finiteness
  refine ⟨C,hC,?_⟩
  intro δ hδ hδhalf hδD f hf hfp
  have hD : 0 < stripDilation V := by dsimp [stripDilation]; positivity
  have hinput : MemLp (stripInput d V f) p volume := by
    exact hfp.indicator ((measurableSet_stripBox d V).preimage
      (projectiveJoin d).symm.continuous.measurable)
  have hnorm := eLpNorm_stripPullback_local hV hf p
  have hmem : MemLp (stripPullback d V f) p volume :=
    hnorm.trans_lt (ENNReal.mul_lt_top hR hinput)
  have hk := (hKbound (stripDilation V*δ) (mul_pos hD hδ) hδD
    (stripPullback d V f) hmem).2
  have hdir := eLpNorm_chartDirection_le (by norm_num : (0:ℝ)<1)
    (OAI.MeasureTheory.Kakeya.measurable_kakeyaMaximal (stripDilation V*δ) _
      (measurable_stripPullback V hf).aestronglyMeasurable) p
  have hpw : eLpNorm (stripMaximal δ V f) p (volume.restrict (closedBall 0 1)) ≤
      ENNReal.ofReal A * eLpNorm
        (OAI.MeasureTheory.Kakeya.kakeyaMaximal (stripDilation V*δ) (stripPullback d V f) ∘ chartDirection d)
        p (volume.restrict (closedBall 0 1)) := by
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' p
      (measurable_stripMaximal δ V hf).aestronglyMeasurable
    filter_upwards [ae_restrict_mem isClosed_closedBall.measurableSet] with x hx
    simpa using
      hpoint δ hδ hδhalf hδD f hf x (by simpa using hx)
  refine hpw.trans ((mul_le_mul' le_rfl hdir).trans ?_)
  refine (mul_le_mul' le_rfl (mul_le_mul' le_rfl hk)).trans ?_
  refine (mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl hnorm))).trans_eq ?_
  dsimp only [C]
  rw [Real.mul_rpow hD.le hδ.le,ENNReal.ofReal_mul hKpos.le,
    ENNReal.ofReal_mul (Real.rpow_nonneg hD.le _)]
  dsimp only [Q,R,p]
  ac_rfl

end OAI.Geometry.Nikodym
