import OAI.Geometry.Nikodym.MeasureTransport

noncomputable section
open _root_.MeasureTheory Set Module
open scoped ENNReal
namespace OAI.Geometry.Nikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem measurable_projective : Measurable (projective : E × ℝ → E × ℝ) := by
  unfold projective
  fun_prop

def projectiveDistortion (a R : ℝ) : ℝ := a⁻¹ + (R+1)/a^2

theorem projectiveDistortion_pos {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) :
    0 < projectiveDistortion a R := by unfold projectiveDistortion; positivity

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem lipschitzOn_projective {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) :
    LipschitzOnWith ⟨projectiveDistortion a R,(projectiveDistortion_pos ha hR).le⟩
      (projective : E × ℝ → E × ℝ) {p | a ≤ |p.2| ∧ ‖p.1‖ ≤ R} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro p hp q hq
  exact dist_projective_le ha hR p q hp.1 hq.1 hq.2

/-- Quantitative projective transport on a bounded strip away from the pole.
No Jacobian formula or unproved change-of-variables premise is used. -/
theorem lintegral_projective_strip
    (μ : Measure (E × ℝ)) [Measure.IsAddHaarMeasure μ]
    {a b R : ℝ} (ha : 0 < a) (hb : 0 < b) (hR : 0 ≤ R)
    {s T : Set (E × ℝ)} (hs : MeasurableSet s) (hT : MeasurableSet T)
    (hstrip : ∀ p ∈ s, a ≤ |p.2| ∧ |p.2| ≤ b ∧ ‖p.1‖ ≤ R)
    (himage : MapsTo projective s T) {F : E × ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ p in s, F p ∂μ) ≤
      ENNReal.ofReal (projectiveDistortion b⁻¹ (R/a)) ^ finrank ℝ (E × ℝ) *
        ∫⁻ q in T, F (projective q) ∂μ := by
  have hRa : 0 ≤ R/a := div_nonneg hR ha.le
  have hmap : MapsTo (projective : E × ℝ → E × ℝ) s
      {q | b⁻¹ ≤ |q.2| ∧ ‖q.1‖ ≤ R/a} := by
    intro p hp
    obtain ⟨hpa,hpb,hpR⟩ := hstrip p hp
    have hp0 : 0 < |p.2| := ha.trans_le hpa
    constructor
    · change b⁻¹ ≤ |p.2⁻¹|
      rw [abs_inv]
      exact inv_anti₀ hp0 hpb
    · change ‖p.2⁻¹ • p.1‖ ≤ R/a
      rw [norm_smul,Real.norm_eq_abs,abs_inv,div_eq_mul_inv]
      calc
        _ ≤ a⁻¹ * R := mul_le_mul (inv_anti₀ ha hpa) hpR
          (norm_nonneg _) (inv_nonneg.mpr ha.le)
        _ = R * a⁻¹ := mul_comm _ _
  have hi : ∀ p ∈ s, projective (projective p) = p := by
    intro p hp
    exact projective_involutive (abs_pos.mp (ha.trans_le (hstrip p hp).1))
  have h := lintegral_restrict_le_of_lipschitz_inverse μ hs hT
    measurable_projective measurable_projective
    (lipschitzOn_projective (inv_pos.mpr hb) hRa) hmap himage hi hF
  simpa only [ENNReal.ofReal_eq_coe_nnreal (projectiveDistortion_pos (inv_pos.mpr hb) hRa).le]
    using! h

end OAI.Geometry.Nikodym
