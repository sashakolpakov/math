import OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.MixedBoundaryComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.Mixed.CoordinateBoundaryCharts
import OAI.AlgebraicGeometry.Resolution.Blowups.LocalBoundaryPartialLabels

/-! # Mixed Boundary Preservation -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! A coordinate-compatible center preserves every label of an arbitrary explicit boundary model. -/

universe u v

variable {k R : Type u} {ι : Type v} [Field k] [CommRing R] [Algebra k R]
  {w : ι → R}

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

/-- Every actual denominator chart preserves the entire mixed family,
including original unit components and the new exceptional component.
The center and the divided-label set use the displayed common coordinates. -/
theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.mixed_coordinate_center_preserves_boundary
    (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w) (C : Finset M.indices) (F : Finset ι)
    (hF : ∀ j, j ∈ F ↔ ∃ s ∈ C, M.coordinate j = some s)
    (a : (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map M.map) :
    LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k (.of (Blowup.Charts.Construction.blowupChart _ a))
      (MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily _ a F w (M.coordinateCenter_boundary_mem C F hF)) := by
  let : Algebra (MvPolynomial M.indices k) R := M.map.toAlgebra
  let : Algebra.Etale (MvPolynomial M.indices k) R := RingHom.etale_algebraMap.mp M.etale
  let : IsScalarTower k (MvPolynomial M.indices k) R :=
    IsScalarTower.of_algebraMap_eq (fun c => (M.ground c).symm)
  have hcanon : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k (.of (Blowup.Charts.Construction.blowupChart ((SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map M.map) a))
      (M.mixedCoordinateFamily C a) :=
    Mixed.CoordinateBoundaryCharts.Construction.exists_mixed_coordinate_boundary_open_chart C a ⟨Subtype.val, Subtype.val_injective⟩
  let u : Option ι → Blowup.Charts.Construction.blowupChart ((SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map M.map) a := fun j => match j with
    | none => 1 | some l => Blowup.Charts.Construction.blowupChartConstants ((SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map M.map) a (M.multiplier l)
  have hu (j : Option ι) : IsUnit (u j) := by
    cases j with
    | none => exact isUnit_one
    | some l => exact (M.multiplierUnit l).map (Blowup.Charts.Construction.blowupChartConstants ((SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map M.map) a)
  apply hcanon.pullbackLabels (OptionalBoundaryLabels.Construction.adjoinPartialBoundaryLabel M.boundaryCoordinate)
    (OptionalBoundaryLabels.Construction.adjoinPartialBoundaryLabel_distinct M.boundaryCoordinate M.boundaryCoordinate_distinct)
    (MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily _ a F w (M.coordinateCenter_boundary_mem C F hF)) u hu
  intro j
  cases j with
  | none => exact M.mixedBoundary_comparison C F hF a none
  | some l =>
      cases hc : M.boundaryCoordinate l with
      | none => simpa only [u, OptionalBoundaryLabels.Construction.adjoinPartialBoundaryLabel, hc, Option.map_none] using
          M.mixedBoundary_comparison C F hF a (some l)
      | some s => simpa only [u, OptionalBoundaryLabels.Construction.adjoinPartialBoundaryLabel, hc, Option.map_some] using
          M.mixedBoundary_comparison C F hF a (some l)

end

end OAI.AlgebraicGeometry.Resolution.Blowups
