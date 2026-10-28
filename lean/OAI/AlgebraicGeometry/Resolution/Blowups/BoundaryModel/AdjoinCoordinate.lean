import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.Operations

/-! # Adjoin Coordinate -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Add a transverse unused coordinate as an actual new boundary equation. -/

universe u v

def Etale.BoundaryModel.Construction.EtaleBoundaryModel.adjoinCoordinate
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    {ι : Type v} {w : ι → R} (M : Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w)
    (s : M.indices) (hs : ∀ j, M.coordinate j ≠ some s) :
    Etale.BoundaryModel.Construction.EtaleBoundaryModel k R (Option ι)
      (fun j => match j with | none => M.map (MvPolynomial.X s) | some j => w j) where
  indices := M.indices
  finite := M.finite
  decidableEq := M.decidableEq
  map := M.map
  etale := M.etale
  ground := M.ground
  coordinate := fun j => match j with | none => some s | some j => M.coordinate j
  distinct i j t hi hj := by
    cases i with
    | none =>
        cases j with
        | none => rfl
        | some j =>
            have ht : s = t := Option.some.inj hi
            exact False.elim (hs j (hj.trans (congrArg some ht.symm)))
    | some i =>
        cases j with
        | none =>
            have ht : s = t := Option.some.inj hj
            exact False.elim (hs i (hi.trans (congrArg some ht.symm)))
        | some j => exact congrArg some (M.distinct i j t hi hj)
  multiplier := fun j => match j with | none => 1 | some j => M.multiplier j
  multiplierUnit j := by
    cases j with
    | none => exact isUnit_one
    | some j => exact M.multiplierUnit j
  equation j := by
    cases j with
    | none => exact (one_mul (M.map (MvPolynomial.X s))).symm
    | some j => exact M.equation j

/-- Retain the specified actual equation when it equals the unused coordinate. -/
def Etale.BoundaryModel.Construction.EtaleBoundaryModel.adjoinEquation
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    {ι : Type v} {w : ι → R} (M : Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w)
    (z : R) (s : M.indices) (hs : ∀ j, M.coordinate j ≠ some s)
    (hz : M.map (MvPolynomial.X s) = z) :
    Etale.BoundaryModel.Construction.EtaleBoundaryModel k R (Option ι) (fun j => match j with | none => z | some j => w j) where
  indices := M.indices
  finite := M.finite
  decidableEq := M.decidableEq
  map := M.map
  etale := M.etale
  ground := M.ground
  coordinate := (M.adjoinCoordinate s hs).coordinate
  distinct := (M.adjoinCoordinate s hs).distinct
  multiplier := (M.adjoinCoordinate s hs).multiplier
  multiplierUnit := (M.adjoinCoordinate s hs).multiplierUnit
  equation j := by
    cases j with
    | none => exact hz.symm.trans (one_mul (M.map (MvPolynomial.X s))).symm
    | some j => exact M.equation j

end

end OAI.AlgebraicGeometry.Resolution.Blowups
