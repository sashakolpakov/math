import OAI.Analysis.PDE.Concentration.Cylinder.Coordinates
import OAI.Analysis.PDE.Concentration.PolarIntegral

namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory Set

noncomputable def cylinderShell (t₀ t₁ a b : ℝ) : Set CylinderSpace :=
  cylinderComplexEquiv ⁻¹' (Icc t₀ t₁ ×ˢ {z : ℂ | ‖z‖ ∈ Icc a b})

theorem cylinderPoint_mem_shell {t₀ t₁ a b t r θ : ℝ}
    (ht : t ∈ Icc t₀ t₁) (hr : r ∈ Icc a b) (hr0 : 0 ≤ r) :
    cylinderPoint t r θ ∈ cylinderShell t₀ t₁ a b := by
  change cylinderComplexEquiv (cylinderPoint t r θ) ∈ Icc t₀ t₁ ×ˢ {z : ℂ | ‖z‖ ∈ Icc a b}
  rw [cylinderComplexEquiv_point]
  exact ⟨ht, by simpa only [Set.mem_ofPred_eq, Complex.norm_polarCoord_symm, abs_of_nonneg hr0] using hr⟩

theorem isCompact_complexAnnulus (a b : ℝ) : IsCompact {z : ℂ | ‖z‖ ∈ Icc a b} := by
  apply (isCompact_closedBall (0 : ℂ) b).of_isClosed_subset
    (isClosed_Icc.preimage continuous_norm)
  intro z hz
  simpa only [Metric.mem_closedBall, dist_zero_right] using hz.2

theorem isCompact_cylinderShell (t₀ t₁ a b : ℝ) : IsCompact (cylinderShell t₀ t₁ a b) := by
  have he : cylinderShell t₀ t₁ a b = cylinderComplexEquiv.symm ''
      (Icc t₀ t₁ ×ˢ {z : ℂ | ‖z‖ ∈ Icc a b}) := by
    exact (cylinderComplexEquiv.toEquiv.image_symm_eq_preimage _).symm
  rw [he]
  exact (isCompact_Icc.prod (isCompact_complexAnnulus a b)).image continuous_cylinderComplexEquiv_symm

theorem cylinderShell_integral {f : CylinderSpace → ℝ} (hf : Continuous f)
    {t₀ t₁ a b : ℝ} (ht : t₀ ≤ t₁) (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in cylinderShell t₀ t₁ a b, f x) =
      ∫ t in t₀..t₁, ∫ r in a..b, r * cylinderAngularAverage f t r := by
  let F : ℝ × ℂ → ℝ := fun p => f (cylinderComplexEquiv.symm p)
  have hF : Continuous F := hf.comp continuous_cylinderComplexEquiv_symm
  have hi : IntegrableOn F (Icc t₀ t₁ ×ˢ {z : ℂ | ‖z‖ ∈ Icc a b}) :=
    hF.continuousOn.integrableOn_compact (isCompact_Icc.prod (isCompact_complexAnnulus a b))
  have he := cylinderComplexEquiv_measurePreserving.setIntegral_preimage_emb
    cylinderComplexEquiv.measurableEmbedding F (Icc t₀ t₁ ×ˢ {z : ℂ | ‖z‖ ∈ Icc a b})
  have he' : (∫ x in cylinderShell t₀ t₁ a b, f x) =
      ∫ p in Icc t₀ t₁ ×ˢ {z : ℂ | ‖z‖ ∈ Icc a b}, F p := by
    simpa only [F, cylinderShell, MeasurableEquiv.symm_apply_apply] using he
  have hp : (∫ p in Icc t₀ t₁ ×ˢ {z : ℂ | ‖z‖ ∈ Icc a b}, F p) =
      ∫ t in Icc t₀ t₁, ∫ z in {z : ℂ | ‖z‖ ∈ Icc a b}, F (t, z) := setIntegral_prod F hi
  rw [he', hp, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le ht]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  have hFt : Continuous (fun z : ℂ => F (t, z)) := hF.comp (continuous_const.prodMk continuous_id)
  rw [complex_annulus_integral hFt ha hab]
  apply intervalIntegral.integral_congr
  intro r _
  dsimp only
  congr 1
  rw [cylinderAngularAverage_eq_centered]
  apply intervalIntegral.integral_congr
  intro θ _
  exact congrArg f (cylinderComplexEquiv_symm_polar t r θ)

end OAI.Analysis.PDE.Concentration
