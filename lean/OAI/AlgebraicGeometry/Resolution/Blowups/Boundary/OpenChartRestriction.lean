import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.ModelRestriction

/-! # Open Chart Restriction -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Keep any injectively selected labels in an actual pointed boundary chart. -/

universe u v t

variable {k : Type u} [CommRing k] {R : CommRingCat.{u}} [Algebra k R]
  {ι : Type v} {κ : Type t} {w : ι → R} {p : PrimeSpectrum R}

def Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart.reindex (C : Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart k R w p) (e : κ ↪ ι) :
    Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart k R (fun j => w (e j)) p where
  carrier := C.carrier
  algebra := C.algebra
  map := C.map
  isOpenImmersion := C.isOpenImmersion
  point := C.point
  point_over := C.point_over
  model := C.model.reindex e

end

end OAI.AlgebraicGeometry.Resolution.Blowups
