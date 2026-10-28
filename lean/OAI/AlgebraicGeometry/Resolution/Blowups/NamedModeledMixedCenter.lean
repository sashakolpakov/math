import OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.MixedBoundaryPreservation

/-! # Named Modeled Mixed Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Apply full mixed-boundary preservation to the actual named center ideal. -/

universe u v

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.mixed_named_center_preserves_boundary
    {k R : Type u} {ι : Type v} [Field k] [CommRing R] [Algebra k R] {w : ι → R}
    (M : Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w) (I : Ideal R) (C : Finset M.indices)
    (hI : I = (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map M.map) (F : Finset ι)
    (hF : ∀ j, j ∈ F ↔ ∃ s ∈ C, M.coordinate j = some s)
    (a : I) (hw : ∀ j ∈ F, w j ∈ I) :
    LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k (.of (Blowup.Charts.Construction.blowupChart I a)) (MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily I a F w hw) := by
  subst I
  exact M.mixed_coordinate_center_preserves_boundary C F hF a

end

end OAI.AlgebraicGeometry.Resolution.Blowups
