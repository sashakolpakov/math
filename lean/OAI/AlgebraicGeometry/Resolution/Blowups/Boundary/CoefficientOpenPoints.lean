import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CoefficientOpenChart

/-! # Coefficient Open Points -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Boundary

noncomputable section

/-! The actual open range and point replacement for a boundary coefficient chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {k : Type u} [CommRing k] {R : CommRingCat.{u}} [Algebra k R]
  {ι : Type v} {w : ι → R} {J : Ideal R} {n : ℕ} {p : PrimeSpectrum R}

def CoefficientOpenChart.Construction.BoundaryCoefficientOpenChart.openRange (C : CoefficientOpenChart.Construction.BoundaryCoefficientOpenChart k R w J n p) :
    TopologicalSpace.Opens (PrimeSpectrum R) :=
  (Spec.map (CommRingCat.ofHom C.map.toRingHom)).opensRange

theorem CoefficientOpenChart.Construction.BoundaryCoefficientOpenChart.point_mem_openRange (C : CoefficientOpenChart.Construction.BoundaryCoefficientOpenChart k R w J n p) :
    p ∈ C.openRange := ⟨C.point, C.point_over⟩

/-- Change only the retained point of the same actual open chart. -/
def CoefficientOpenChart.Construction.BoundaryCoefficientOpenChart.atPoint (C : CoefficientOpenChart.Construction.BoundaryCoefficientOpenChart k R w J n p)
    (q : PrimeSpectrum R) (Q : PrimeSpectrum C.carrier)
    (hQ : PrimeSpectrum.comap C.map.toRingHom Q = q) (hz : C.normal ∈ Q.asIdeal) :
    CoefficientOpenChart.Construction.BoundaryCoefficientOpenChart k R w J n q :=
  { C with point := Q, point_over := hQ, normal_mem_point := hz }

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Boundary
