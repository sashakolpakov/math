import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.BoundaryModel

/-! # Transverse Boundary Open -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.TransverseBoundaryOpen.Construction

noncomputable section

/-! An actual boundary open whose coordinates retain a specified transverse equation. -/

universe u v

structure TransverseBoundaryOpenChart (k : Type u) [CommRing k]
    (R : CommRingCat.{u}) [Algebra k R] {ι : Type v} (w : ι → R)
    (z : R) (p : PrimeSpectrum R) where
  chart : Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart k R w p
  normalIndex : chart.model.indices
  normal_eq : chart.model.map (MvPolynomial.X normalIndex) = chart.map z
  normal_unused : ∀ j, chart.model.coordinate j ≠ some normalIndex

end

end OAI.AlgebraicGeometry.Resolution.Blowups.TransverseBoundaryOpen.Construction
