import OAI.Analysis.PDE.Elliptic.TailIntegral

open Set _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {X : Type*} [MeasurableSpace X]

/-- A geometric superlevel tail controls a positive moment, with
constants chosen before the measure and the function. -/
theorem geometric_tail_moment {M theta : ℝ} (hM : 1 < M)
    (htheta : 0 < theta) (htheta1 : theta < 1) :
    ∃ p C : ℝ, 0 < p ∧ 0 < C ∧ ∀ (mu : Measure X) (u : X → ℝ), Measurable u →
      (∀ k : ℕ, mu {x | M ^ k < u x} ≤ ENNReal.ofReal theta ^ k * mu univ) →
      ∫⁻ x, ENNReal.ofReal (u x) ^ p ∂mu ≤ ENNReal.ofReal C * mu univ := by
  obtain ⟨p, hp, hqreal⟩ := exists_moment_exponent hM htheta1
  have hM0 : 0 < M := zero_lt_one.trans hM
  let a : ℝ≥0∞ := ENNReal.ofReal M ^ p
  let q : ℝ≥0∞ := a * ENNReal.ofReal theta
  have hqeq : q = ENNReal.ofReal (theta * M ^ p) := by
    dsimp [q, a]
    rw [ENNReal.ofReal_mul htheta.le, ENNReal.ofReal_rpow_of_pos hM0]
    exact mul_comm _ _
  have hq : q < 1 := by
    rw [hqeq]
    exact ENNReal.ofReal_lt_one.mpr hqreal
  have ha : a ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top
  have hs : (∑' k : ℕ, q ^ k) ≠ ⊤ := (tsum_geometric_lt_top.mpr hq).ne
  let K : ℝ≥0∞ := 1 + a * ∑' k : ℕ, q ^ k
  have hK : K ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨by simp, ENNReal.mul_ne_top ha hs⟩
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one le_self_add
  refine ⟨p, K.toReal, hp, ENNReal.toReal_pos hKpos.ne' hK, ?_⟩
  intro mu u hu htail
  rw [ENNReal.ofReal_toReal hK]
  exact lintegral_rpow_le_geometric_tail mu hu hM hp.le htail

end OAI.Analysis.PDE.Elliptic
