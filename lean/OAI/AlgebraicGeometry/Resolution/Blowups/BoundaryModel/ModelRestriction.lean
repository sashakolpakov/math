import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.BoundaryModel

/-! # Model Restriction -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Restrict a boundary model to any injectively selected collection of labels. -/

universe u v t

variable {k A : Type u} {ι : Type v} {κ : Type t} [CommRing k] [CommRing A]
  [Algebra k A] {w : ι → A}

def Etale.BoundaryModel.Construction.EtaleBoundaryModel.reindex (M : Etale.BoundaryModel.Construction.EtaleBoundaryModel k A ι w) (e : κ ↪ ι) :
    Etale.BoundaryModel.Construction.EtaleBoundaryModel k A κ (fun j => w (e j)) where
  indices := M.indices
  finite := M.finite
  decidableEq := M.decidableEq
  map := M.map
  etale := M.etale
  ground := M.ground
  coordinate := fun j => M.coordinate (e j)
  distinct i j s hi hj := e.injective (M.distinct (e i) (e j) s hi hj)
  multiplier := fun j => M.multiplier (e j)
  multiplierUnit := fun j => M.multiplierUnit (e j)
  equation := fun j => M.equation (e j)

end

end OAI.AlgebraicGeometry.Resolution.Blowups
