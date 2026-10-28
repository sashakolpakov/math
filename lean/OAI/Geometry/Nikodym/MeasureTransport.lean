import OAI.Geometry.Nikodym.Projective

noncomputable section
open _root_.MeasureTheory Set Module
open scoped ENNReal
namespace OAI.Geometry.Nikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A Lipschitz map changes any finite-dimensional Haar volume by at most
its Lipschitz constant to the ambient dimension. The normalization cancels
through the genuine Hausdorff/Haar comparison. -/
theorem haar_image_le_of_lipschitzOn (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {K : NNReal} {f : E → E} {s : Set E} (hf : LipschitzOnWith K f s) :
    μ (f '' s) ≤ (K : ℝ≥0∞) ^ finrank ℝ E * μ s := by
  let ν : Measure E := Measure.hausdorffMeasure (finrank ℝ E)
  let c : NNReal := Measure.addHaarScalarFactor ν μ
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν μ
  have he : ν = c • μ := Measure.isAddLeftInvariant_eq_smul ν μ
  have h := hf.hausdorffMeasure_image_le (by positivity : (0 : ℝ) ≤ finrank ℝ E)
  change ν (f '' s) ≤ (K : ℝ≥0∞) ^ (finrank ℝ E : ℝ) * ν s at h
  rw [he,Measure.smul_apply,Measure.smul_apply] at h
  change (c : ℝ≥0∞) * μ (f '' s) ≤
    (K : ℝ≥0∞) ^ (finrank ℝ E : ℝ) * ((c : ℝ≥0∞) * μ s) at h
  rw [ENNReal.rpow_natCast] at h
  apply (ENNReal.mul_le_mul_iff_left (by exact_mod_cast hc.ne') ENNReal.coe_ne_top).mp
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h

/-- A local inverse with bounded Lipschitz constant controls the pullback
measure. Only inverse identities on the actual source set are required. -/
theorem map_restrict_le_of_lipschitz_inverse (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {K : NNReal} {f g : E → E} {s t : Set E}
    (hf : Measurable f) (hg : LipschitzOnWith K g t)
    (hmap : MapsTo f s t) (hinv : ∀ x ∈ s, g (f x) = x) :
    Measure.map f (μ.restrict s) ≤ (K : ℝ≥0∞) ^ finrank ℝ E • μ := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.map_apply hf hA,Measure.restrict_apply (hf hA),Measure.smul_apply,smul_eq_mul]
  have hs : f ⁻¹' A ∩ s ⊆ g '' (A ∩ t) := by
    intro x hx
    exact ⟨f x,⟨hx.1,hmap hx.2⟩,hinv x hx.2⟩
  exact (measure_mono hs).trans ((haar_image_le_of_lipschitzOn μ
    (hg.mono inter_subset_right)).trans (mul_le_mul' le_rfl (measure_mono inter_subset_left)))

theorem lintegral_comp_restrict_le_of_lipschitz_inverse
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {K : NNReal} {f g : E → E} {s t : Set E}
    (hf : Measurable f) (hg : LipschitzOnWith K g t)
    (hmap : MapsTo f s t) (hinv : ∀ x ∈ s, g (f x) = x)
    {F : E → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ x in s, F (f x) ∂μ) ≤ (K : ℝ≥0∞) ^ finrank ℝ E * ∫⁻ y, F y ∂μ := by
  rw [← lintegral_map hF hf]
  calc
    _ ≤ ∫⁻ y, F y ∂((K : ℝ≥0∞) ^ finrank ℝ E • μ) :=
      lintegral_mono' (map_restrict_le_of_lipschitz_inverse μ hf hg hmap hinv) le_rfl
    _ = _ := lintegral_smul_measure _ _

/-- Integral transport on actual source and target sets; the inverse is
required only along the source, not globally. -/
theorem lintegral_restrict_le_of_lipschitz_inverse
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {K : NNReal} {f g : E → E} {s t T : Set E}
    (hs : MeasurableSet s) (hT : MeasurableSet T)
    (hf : Measurable f) (hgmeas : Measurable g) (hg : LipschitzOnWith K g t)
    (hmap : MapsTo f s t) (hmapT : MapsTo f s T)
    (hinv : ∀ x ∈ s, g (f x) = x)
    {F : E → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ x in s, F x ∂μ) ≤ (K : ℝ≥0∞) ^ finrank ℝ E * ∫⁻ y in T, F (g y) ∂μ := by
  have he : (∫⁻ x in s, F x ∂μ) =
      ∫⁻ x in s, T.indicator (F ∘ g) (f x) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hs] with x hx
    simp only [Set.indicator_of_mem (hmapT hx), Function.comp_apply, hinv x hx]
  rw [he]
  have h := lintegral_comp_restrict_le_of_lipschitz_inverse μ hf hg hmap hinv
    ((hF.comp hgmeas).indicator hT)
  simpa only [lintegral_indicator hT, Function.comp_apply] using h

theorem eLpNorm_indicator_comp_le_of_lipschitz_inverse
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {K : NNReal} {f g : E → E} {s t : Set E}
    (hs : MeasurableSet s) (hf : Measurable f) (hg : LipschitzOnWith K g t)
    (hmap : MapsTo f s t) (hinv : ∀ x ∈ s, g (f x) = x)
    {F : E → ℂ} (hF : Measurable F) (p : ℝ≥0∞) :
    eLpNorm (s.indicator (F ∘ f)) p μ ≤
      ((K : ℝ≥0∞) ^ finrank ℝ E) ^ (1/p).toReal * eLpNorm F p μ := by
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs,
    ← eLpNorm_map_measure hF.aestronglyMeasurable hf.aemeasurable]
  exact eLpNorm_le_of_measure_le_smul (map_restrict_le_of_lipschitz_inverse μ hf hg hmap hinv)

end OAI.Geometry.Nikodym
