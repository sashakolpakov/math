import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.BoundaryModel

/-! # Equation Congruence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Pointwise equation replacement preserving the model's exact coordinate data. -/

universe u v

def Etale.BoundaryModel.Construction.EtaleBoundaryModel.congrEquations
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    {ι : Type v} {w : ι → R} (M : Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w)
    (v : ι → R) (hv : ∀ j, v j = w j) : Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι v where
  indices := M.indices
  finite := M.finite
  decidableEq := M.decidableEq
  map := M.map
  etale := M.etale
  ground := M.ground
  coordinate := M.coordinate
  distinct := M.distinct
  multiplier := M.multiplier
  multiplierUnit := M.multiplierUnit
  equation j := (hv j).trans (M.equation j)

end

end OAI.AlgebraicGeometry.Resolution.Blowups
