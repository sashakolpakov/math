import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.LocalCenterPreservation
import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.LocalOutsideCenter

/-! # Admissible Preservation -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.AdmissiblePreservation.Construction

noncomputable section

/-! Full accumulated boundary geometry survives every locally coordinate-compatible blowup. -/

universe u v

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

/-- Every prime of every actual denominator chart retains the full
original mixed family and the new exceptional label. Common coordinates
are required only along the center; the complement uses its actual
unit-denominator neighborhoods. -/
theorem hasEtaleBoundaryCharts_mixed_admissible_blowup
    {k : Type u} [Field k] (R : CommRingCat.{u}) [Algebra k R]
    (I : Ideal R) {ι : Type v} (w : ι → R) (F : Finset ι) (hw : ∀ j ∈ F, w j ∈ I)
    (hboundary : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R w) (hcenter : CenterCharts.Construction.HasMixedBoundaryCenterCharts k R I w F)
    (a : I) :
    LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k (.of (Blowup.Charts.Construction.blowupChart I a)) (Equations.Construction.blowupMixedBoundaryFamily I a F w hw) := by
  classical
  intro p
  by_cases hp : I ≤ (PrimeSpectrum.comap (Blowup.Charts.Construction.blowupChartConstants I a) p).asIdeal
  · obtain ⟨C⟩ := hcenter (PrimeSpectrum.comap (Blowup.Charts.Construction.blowupChartConstants I a) p) hp
    exact LocalCenterPreservation.Construction.exists_mixed_boundary_open_chart_of_center_chart k R I w F hw a p C
  · exact LocalOutsideCenter.Construction.exists_local_mixed_boundary_open_chart_outside_center k R I w F hw hboundary a p hp

end

end OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.AdmissiblePreservation.Construction
