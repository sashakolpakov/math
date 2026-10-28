import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.PartialLabels
import OAI.AlgebraicGeometry.Resolution.Blowups.LocalBoundaryProperty

/-! # Local Boundary Partial Labels -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Local boundary models retain all labels under a partial injection with unit equations. -/

universe u v t

variable {k : Type u} [CommRing k] {R : CommRingCat.{u}} [Algebra k R]
  {ι : Type v} {κ : Type t} {w : κ → R} {p : PrimeSpectrum R}

def Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart.pullbackLabels (C : Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart k R w p)
    (r : ι → Option κ) (hr : ∀ i j s, r i = some s → r j = some s → i = j)
    (v u : ι → R) (hu : ∀ j, IsUnit (u j))
    (hv : ∀ j, v j = u j * (match r j with | none => 1 | some s => w s)) :
    Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart k R v p := by
  refine
    { carrier := C.carrier
      algebra := C.algebra
      map := C.map
      isOpenImmersion := C.isOpenImmersion
      point := C.point
      point_over := C.point_over
      model := C.model.pullbackLabels r hr (fun j => C.map (v j)) (fun j => C.map (u j))
        (fun j => (hu j).map C.map.toRingHom) ?_ }
  intro j
  rw [hv j, map_mul]
  cases hrj : r j with
  | none => rw [map_one]
  | some s => rfl

theorem LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts.pullbackLabels (h : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R w)
    (r : ι → Option κ) (hr : ∀ i j s, r i = some s → r j = some s → i = j)
    (v u : ι → R) (hu : ∀ j, IsUnit (u j))
    (hv : ∀ j, v j = u j * (match r j with | none => 1 | some s => w s)) :
    LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R v := by
  intro p
  obtain ⟨C⟩ := h p
  exact ⟨C.pullbackLabels r hr v u hu hv⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
