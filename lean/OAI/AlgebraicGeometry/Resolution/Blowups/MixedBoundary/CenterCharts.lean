import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.BoundaryModel

/-! # Center Charts -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.CenterCharts.Construction

noncomputable section

/-! Actual common coordinates for a center and all its divided or transverse boundary labels. -/

universe u v

structure MixedBoundaryCoordinateCenterOpenChart (k : Type u) [CommRing k]
    (R : CommRingCat.{u}) [Algebra k R] (I : Ideal R) {ι : Type v}
    (w : ι → R) (F : Finset ι) (p : PrimeSpectrum R) where
  chart : Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart k R w p
  coordinates : Finset chart.model.indices
  center_eq : I.map chart.map.toRingHom = (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal coordinates).map chart.model.map
  divided_iff : ∀ j, j ∈ F ↔ ∃ s ∈ coordinates, chart.model.coordinate j = some s

/-- Only points on the center require common coordinate data. The
complement is handled by the actual isomorphic blowup charts. -/
def HasMixedBoundaryCenterCharts (k : Type u) [CommRing k]
    (R : CommRingCat.{u}) [Algebra k R] (I : Ideal R) {ι : Type v}
    (w : ι → R) (F : Finset ι) : Prop :=
  ∀ p : PrimeSpectrum R, I ≤ p.asIdeal → Nonempty (MixedBoundaryCoordinateCenterOpenChart k R I w F p)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.CenterCharts.Construction
