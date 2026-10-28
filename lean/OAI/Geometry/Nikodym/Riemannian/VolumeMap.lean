import OAI.Geometry.Nikodym.Riemannian.VolumeIntegral

open Set _root_.MeasureTheory
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Geometry.Nikodym.SmoothCoordinateMetric

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Exact coordinate invariance of the measure defined by the metric density.
Only injectivity, differentiability, and the actual pullback metric identity
are needed; no independent volume-preservation premise occurs. -/
theorem map_coordinateVolume_restrict (g h : SmoothCoordinateMetric E)
    {S : Set E} {F : E → E} {J : E → E →L[ℝ] E}
    (hS : MeasurableSet S) (hSD : S ⊆ g.domain) (hFD : MapsTo F S h.domain)
    (hder : ∀ x ∈ S, HasFDerivWithinAt F (J x) S x) (hinj : InjOn F S)
    (hpull : ∀ x ∈ S, ∀ u v, g.inner x u v = h.inner (F x) (J x u) (J x v)) :
    Measure.map F (g.coordinateVolume.restrict S) =
      h.coordinateVolume.restrict (F '' S) := by
  have hc : ContinuousOn F S := fun x hx => (hder x hx).continuousWithinAt
  have hm : AEMeasurable F (g.coordinateVolume.restrict S) := hc.aemeasurable hS
  refine Measure.ext_of_lintegral _ fun φ hφ => ?_
  rw [lintegral_map' hφ.aemeasurable hm]
  exact (g.lintegral_image_coordinateVolume h hS hSD hFD hder hinj hpull φ).symm

end OAI.Geometry.Nikodym.SmoothCoordinateMetric
