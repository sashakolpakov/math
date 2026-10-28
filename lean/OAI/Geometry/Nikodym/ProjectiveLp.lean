import OAI.Geometry.Nikodym.ProjectiveIntegral

noncomputable section
open _root_.MeasureTheory Set Module
open scoped ENNReal
namespace OAI.Geometry.Nikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A truncated projective pullback is bounded on every `Lᵖ`.
The norm distortion is derived from the actual inverse geometry. -/
theorem eLpNorm_projective_truncated
    (μ : Measure (E × ℝ)) [Measure.IsAddHaarMeasure μ]
    {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R)
    {s : Set (E × ℝ)} (hs : MeasurableSet s)
    (hstrip : ∀ q ∈ s, a ≤ |q.2| ∧ ‖q.1‖ ≤ R)
    {F : E × ℝ → ℂ} (hF : Measurable F) (p : ℝ≥0∞) :
    eLpNorm (fun q => s.indicator F (projective q)) p μ ≤
      (ENNReal.ofReal (projectiveDistortion a R) ^ finrank ℝ (E × ℝ)) ^
        (1/p).toReal * eLpNorm F p μ := by
  let K : NNReal := ⟨projectiveDistortion a R,(projectiveDistortion_pos ha hR).le⟩
  have hLip : LipschitzOnWith K (projective : E × ℝ → E × ℝ) s :=
    (lipschitzOn_projective ha hR).mono hstrip
  have hmap : MapsTo (projective : E × ℝ → E × ℝ) (projective ⁻¹' s) s :=
    fun _ hq => hq
  have hi : ∀ q ∈ projective ⁻¹' s, projective (projective q) = q := by
    intro q hq
    have h := (hstrip (projective q) hq).1
    have hq0 : q.2 ≠ 0 := by
      intro hz
      simp only [projective,hz,inv_zero,abs_zero] at h
      linarith
    exact projective_involutive hq0
  have h := eLpNorm_indicator_comp_le_of_lipschitz_inverse μ
    (hs.preimage measurable_projective) measurable_projective hLip hmap hi hF p
  have he : (fun q => s.indicator F (projective q)) =
      (projective ⁻¹' s).indicator (F ∘ projective) := by
    ext q
    by_cases hq : projective q ∈ s <;> simp [hq]
  rw [he]
  simpa only [K,ENNReal.ofReal_eq_coe_nnreal (projectiveDistortion_pos ha hR).le] using! h

end OAI.Geometry.Nikodym
