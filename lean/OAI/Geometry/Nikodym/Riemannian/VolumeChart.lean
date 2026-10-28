import OAI.Geometry.Nikodym.Riemannian.VolumeBeltrami
import OAI.Geometry.Nikodym.SpaceFormChart

open Set _root_.MeasureTheory
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Geometry.Nikodym.LocalBeltramiChart

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
variable {g : SmoothCoordinateMetric (EuclideanSpace ℝ (Fin n))} {κ : ℝ}
  {x₀ : EuclideanSpace ℝ (Fin n)}
variable (C : LocalBeltramiChart g κ x₀)

/-- The chart constructed from constant curvature preserves genuine
Riemannian volume, expressed in the explicit Beltrami coordinates. -/
theorem map_volume_restrict {S : Set E} (hS : MeasurableSet S)
    (hSC : S ⊆ C.chart.source) :
    Measure.map C.chart (g.coordinateVolume.restrict S) =
      (beltramiVolume κ).restrict (C.chart '' S) := by
  apply map_coordinateVolume_beltrami g κ hS (hSC.trans C.source_domain)
    (fun x hx => C.positive x (hSC hx))
  · intro x hx
    exact (((C.smooth x (hSC hx)).contDiffAt
      (C.chart.open_source.mem_nhds (hSC hx))).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
  · exact C.chart.injOn.mono hSC
  · intro x hx
    exact C.metric x (hSC hx)

theorem map_volume_source :
    Measure.map C.chart (g.coordinateVolume.restrict C.chart.source) =
      (beltramiVolume κ).restrict C.chart.target := by
  simpa only [C.chart.image_source_eq_target] using
    C.map_volume_restrict C.chart.open_source.measurableSet Subset.rfl

/-- Explicit comparable-volume constants on every sufficiently small
subchart; these are consequences of the actual metric determinant. -/
theorem map_volume_restrict_bounds {S : Set E} (hS : MeasurableSet S)
    (hSC : S ⊆ C.chart.source)
    (hsmall : ∀ y ∈ C.chart '' S, |κ| * ‖y‖^2 ≤ 1/2) :
    ENNReal.ofReal (Real.sqrt ((2/3 : ℝ)^(n+1))) • volume.restrict (C.chart '' S) ≤
        Measure.map C.chart (g.coordinateVolume.restrict S) ∧
      Measure.map C.chart (g.coordinateVolume.restrict S) ≤
        ENNReal.ofReal (Real.sqrt ((2 : ℝ)^(n+1))) • volume.restrict (C.chart '' S) := by
  rw [C.map_volume_restrict hS hSC]
  apply beltramiVolume_restrict_bounds _ hsmall
  exact hS.image_of_continuousOn_injOn (C.chart.continuousOn.mono hSC)
    (C.chart.injOn.mono hSC)

end OAI.Geometry.Nikodym.LocalBeltramiChart
