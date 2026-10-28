import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.CenterCharts
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Center Generalization -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Actual common-center open charts also cover every generalization of their marked point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

def MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart.generalization
    {k : Type u} [CommRing k] {R : CommRingCat.{u}} [Algebra k R]
    {ι : Type v} {I : Ideal R} {w : ι → R} {F : Finset ι} {p q : PrimeSpectrum R}
    (C : MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k R I w F q) (hpq : p ≤ q) :
    MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k R I w F p := by
  let j := Spec.map (CommRingCat.ofHom C.chart.map.toRingHom)
  have hq : q ∈ j.opensRange := ⟨C.chart.point, C.chart.point_over⟩
  have hp : p ∈ j.opensRange :=
    ((PrimeSpectrum.le_iff_specializes p q).mp hpq).mem_open j.opensRange.isOpen hq
  let P := hp.choose
  have hP := hp.choose_spec
  exact {
    chart := { C.chart with point := P, point_over := hP }
    coordinates := C.coordinates
    center_eq := C.center_eq
    divided_iff := C.divided_iff }

end

end OAI.AlgebraicGeometry.Resolution.Blowups
