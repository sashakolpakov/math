import OAI.Geometry.Nikodym.BallMass

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped ENNReal
namespace OAI.Geometry.Nikodym

def ballAverage {d : ℕ} (δ K : ℝ) (f : Space (d+1) → ℂ) (x : Space (d+1)) : ℝ≥0∞ :=
  ballMass (K*δ) f x / ENNReal.ofReal (δ^d)

theorem measurable_ballAverage {d : ℕ} (δ K : ℝ) {f : Space (d+1) → ℂ}
    (hf : Measurable f) : Measurable (ballAverage δ K f) :=
  (measurable_ballMass _ hf).div_const _

theorem ballAverage_lp_le {d : ℕ} {δ : ℝ} (hδ : 0 < δ) (K : ℝ)
    {f : Space (d+1) → ℂ} (hf : Measurable f) :
    eLpNorm (ballAverage δ K f) (d+1 : ℕ) volume ≤
      (ENNReal.ofReal δ * volume (ball (0:Space (d+1)) K)) * eLpNorm f (d+1 : ℕ) volume := by
  have hn : eLpNorm (ballAverage δ K f) (d+1 : ℕ) volume ≤
      (ENNReal.ofReal (δ^d))⁻¹ * eLpNorm (ballMass (K*δ) f) (d+1 : ℕ) volume := by
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' _ (measurable_ballAverage δ K hf).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => by simp [ballAverage,div_eq_mul_inv,mul_comm])
  apply hn.trans ((mul_le_mul' le_rfl (ballMass_lp_le (K*δ) hf)).trans_eq ?_)
  have hv := Measure.addHaar_ball_mul_of_pos (volume : Measure (Space (d+1))) 0 hδ K
  simp only [Space,finrank_euclideanSpace_fin] at hv
  rw [mul_comm K δ,hv,ENNReal.ofReal_pow hδ.le,ENNReal.ofReal_pow hδ.le,pow_succ]
  calc
    _ = ((ENNReal.ofReal δ)^d)⁻¹ * (ENNReal.ofReal δ)^d *
        (ENNReal.ofReal δ * volume (ball (0:Space (d+1)) K) * eLpNorm f (d+1 : ℕ) volume) := by ac_rfl
    _ = _ := by
      rw [ENNReal.inv_mul_cancel (by positivity) (by finiteness),one_mul]

theorem exists_ballAverage_lp_bound (d : ℕ) (K : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → ∀ f : Space (d+1) → ℂ, Measurable f →
      eLpNorm (ballAverage δ K f) (d+1 : ℕ) volume ≤
        ENNReal.ofReal (C*δ) * eLpNorm f (d+1 : ℕ) volume := by
  let B := volume (ball (0:Space (d+1)) K)
  have hB : B ≠ ⊤ := measure_ball_lt_top.ne
  refine ⟨B.toReal+1,by positivity,?_⟩
  intro δ hδ f hf
  apply (ballAverage_lp_le hδ K hf).trans
  apply mul_le_mul' _ le_rfl
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ B.toReal+1),mul_comm (ENNReal.ofReal δ)]
  apply mul_le_mul' _ le_rfl
  calc
    B = ENNReal.ofReal B.toReal := (ENNReal.ofReal_toReal hB).symm
    _ ≤ ENNReal.ofReal (B.toReal+1) := ENNReal.ofReal_le_ofReal (by linarith)

end OAI.Geometry.Nikodym
