import OAI.Geometry.Nikodym.Riemannian.VolumeChange

open Set _root_.MeasureTheory
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Geometry.Nikodym.SmoothCoordinateMetric

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

theorem lintegral_coordinateVolume_restrict (g : SmoothCoordinateMetric E)
    {S : Set E} (hS : MeasurableSet S) (hSD : S ⊆ g.domain) (φ : E → ℝ≥0∞) :
    ∫⁻ x in S, φ x ∂g.coordinateVolume =
      ∫⁻ x in S, ENNReal.ofReal (g.volumeDensity x) * φ x := by
  rw [g.coordinateVolume_restrict hS hSD]
  exact lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _
    ((g.continuousOn_volumeDensity.mono hSD).aemeasurable hS).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) φ

/-- Genuine change of coordinates for Riemannian volume. The metric pullback
identity supplies precisely the absolute Jacobian required by change of variables.
No measure-comparison or volume-invariance assumption is made. -/
theorem lintegral_image_coordinateVolume (g h : SmoothCoordinateMetric E)
    {S : Set E} {F : E → E} {J : E → E →L[ℝ] E}
    (hS : MeasurableSet S) (hSD : S ⊆ g.domain) (hFD : MapsTo F S h.domain)
    (hder : ∀ x ∈ S, HasFDerivWithinAt F (J x) S x) (hinj : InjOn F S)
    (hpull : ∀ x ∈ S, ∀ u v, g.inner x u v = h.inner (F x) (J x u) (J x v))
    (φ : E → ℝ≥0∞) :
    ∫⁻ y in F '' S, φ y ∂h.coordinateVolume =
      ∫⁻ x in S, φ (F x) ∂g.coordinateVolume := by
  have hFS := measurable_image_of_fderivWithin hS hder hinj
  have hFSD : F '' S ⊆ h.domain := by
    rintro y ⟨x,hx,rfl⟩
    exact hFD hx
  rw [h.lintegral_coordinateVolume_restrict hFS hFSD,
    g.lintegral_coordinateVolume_restrict hS hSD,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS hder hinj]
  apply setLIntegral_congr_fun hS
  intro x hx
  dsimp only
  rw [g.volumeDensity_pullback h (hpull x hx),
    ENNReal.ofReal_mul (abs_nonneg _),mul_assoc]

end OAI.Geometry.Nikodym.SmoothCoordinateMetric
