import OAI.Analysis.Fourier.Restriction.BumpBounds
import OAI.Analysis.Fourier.Restriction.UnitBallLoss

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal BigOperators
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

/-- The small-loss physical-space estimate controls finite exponential
sums on every unit-separated set, with no dependence on its cardinality
other than the displayed strict power. -/
theorem bounded_phases_of_unit_ball_loss {n : ℕ} {p ε : ℝ} (hp : 0 < p)
    (_ : 0 < ε) {A : ℝ≥0∞} (hAt : A ≠ ⊤)
    (hbound : ∀ E : Finset (Space n), ∀ M : ℕ, 1 ≤ M → E.card ≤ M →
      ∀ f : Space n → ℂ, Measurable f → Integrable f →
        (∀ x, (∀ e ∈ E, x ∉ ball e 1) → f x = 0) →
          eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
            A * ENNReal.ofReal ((M : ℝ) ^ ε) * eLpNorm f (ENNReal.ofReal p) volume) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ E : Finset (Space n),
      (∀ z ∈ E, ∀ w ∈ E, z ≠ w → 1 ≤ dist z w) →
      ∀ a : Space n → ℂ, (∀ z ∈ E, ‖a z‖ ≤ 1) →
        eLpNorm (finitePhaseSum E a) (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
          B * ENNReal.ofReal ((E.card : ℝ) ^ (ε + 1 / p)) := by
  let V := volume (ball (0 : Space n) (1 / 4))
  let c := ENNReal.ofReal (V.toReal / 2)
  have hVt : V ≠ ⊤ := measure_ball_lt_top.ne
  have hVp : 0 < V := measure_ball_pos volume _ (by norm_num)
  have hcp : 0 < c := ENNReal.ofReal_pos.mpr (by
    exact div_pos (ENNReal.toReal_pos hVp.ne' hVt) (by norm_num))
  have hct : c ≠ ⊤ := ENNReal.ofReal_ne_top
  refine ⟨c⁻¹ * A * V ^ (1 / p), ?_, ?_⟩
  · apply ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hcp.ne') hAt)
    exact ENNReal.rpow_ne_top_of_nonneg (by positivity) hVt
  intro E hsep a ha
  by_cases he : E.Nonempty
  · have hM : 1 ≤ E.card := he.card_pos
    have HM : 0 < (E.card : ℝ) := by exact_mod_cast he.card_pos
    have H := hbound E E.card hM le_rfl (separatedBumpSum E a)
      (measurable_separatedBumpSum E a) (integrable_separatedBumpSum E a) (by
        intro x hx
        apply separatedBumpSum_eq_zero
        intro z hz hxz
        exact hx z hz (ball_subset_ball (by norm_num) hxz))
    have HL := eLpNorm_finitePhaseSum_le_bumps E a (ENNReal.ofReal p)
    have HN := eLpNorm_separatedBumpSum_le hp E a hsep ha
    have HP : ENNReal.ofReal ((E.card : ℝ) ^ ε) *
        ((E.card : ℝ≥0∞) * V) ^ (1 / p) =
        V ^ (1 / p) * ENNReal.ofReal ((E.card : ℝ) ^ (ε + 1 / p)) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
      have hcN : (E.card : ℝ≥0∞) = ENNReal.ofReal (E.card : ℝ) := by simp
      rw [hcN, ENNReal.ofReal_rpow_of_pos HM,
        Real.rpow_add HM, ENNReal.ofReal_mul (by positivity)]
      ring
    calc
      _ = c⁻¹ * (c * eLpNorm (finitePhaseSum E a) (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hcp.ne' hct, one_mul]
      _ ≤ c⁻¹ * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier (separatedBumpSum E a)) (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
        gcongr
        exact HL
      _ ≤ c⁻¹ * (A * ENNReal.ofReal ((E.card : ℝ) ^ ε) *
          eLpNorm (separatedBumpSum E a) (ENNReal.ofReal p) volume) := by gcongr
      _ ≤ c⁻¹ * (A * ENNReal.ofReal ((E.card : ℝ) ^ ε) *
          ((E.card : ℝ≥0∞) * V) ^ (1 / p)) := by gcongr
      _ = _ := by rw [mul_assoc A, HP]; ring
  · have he0 : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    subst E
    have hP : finitePhaseSum (∅ : Finset (Space n)) a = 0 := by
      funext x
      simp [finitePhaseSum]
    rw [hP, eLpNorm_zero]
    exact zero_le

end OAI.Analysis.Fourier.Restriction
