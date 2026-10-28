import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.CenterCharts
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.PartialLabels

/-! # Center Partial Labels -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Restore unit labels in actual common-coordinate center charts. -/

universe u v t

def MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart.pullbackLabels
    {k : Type u} [CommRing k] {R : CommRingCat.{u}} [Algebra k R]
    {ι : Type v} {κ : Type t} {I : Ideal R} {w : κ → R} {G : Finset κ} {p : PrimeSpectrum R}
    (C : MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k R I w G p)
    (r : ι → Option κ) (hr : ∀ i j s, r i = some s → r j = some s → i = j)
    (v u : ι → R) (hu : ∀ j, IsUnit (u j))
    (hv : ∀ j, v j = u j * (match r j with | none => 1 | some s => w s))
    (F : Finset ι) (hF : ∀ j, j ∈ F ↔ ∃ s ∈ G, r j = some s) :
    MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k R I v F p := by
  let B : Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart k R v p :=
    { carrier := C.chart.carrier
      algebra := C.chart.algebra
      map := C.chart.map
      isOpenImmersion := C.chart.isOpenImmersion
      point := C.chart.point
      point_over := C.chart.point_over
      model := C.chart.model.pullbackLabels r hr (fun j => C.chart.map (v j))
        (fun j => C.chart.map (u j)) (fun j => (hu j).map C.chart.map.toRingHom)
        (by
          intro j
          rw [hv j, map_mul]
          cases r j <;> simp only [map_one]) }
  refine { chart := B
           coordinates := C.coordinates
           center_eq := C.center_eq
           divided_iff := ?_ }
  intro j
  change j ∈ F ↔ ∃ s ∈ C.coordinates, (r j).bind C.chart.model.coordinate = some s
  rw [hF j]
  cases hrj : r j with
  | none => simp
  | some a =>
      simp only [Option.bind_some, Option.some.injEq]
      constructor
      · rintro ⟨s, hs, he⟩
        subst s
        exact (C.divided_iff a).mp hs
      · intro h
        exact ⟨a, (C.divided_iff a).mpr h, rfl⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
