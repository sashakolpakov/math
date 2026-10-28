import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.BoundaryModel

/-! # Operations -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Preserve explicit boundary models under actual étale maps and invertible equation changes. -/

universe u v

variable {k R S : Type u} {ι : Type v} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S] {w : ι → R}

def Etale.BoundaryModel.Construction.EtaleBoundaryModel.baseChange (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w)
    (f : R →ₐ[k] S) (hf : f.toRingHom.Etale) :
    Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k S ι (fun j => f (w j)) where
  indices := M.indices
  finite := M.finite
  decidableEq := M.decidableEq
  map := f.toRingHom.comp M.map
  etale := RingHom.Etale.stableUnderComposition _ _ M.etale hf
  ground c := by
    change f (M.map (MvPolynomial.C c)) = _
    rw [M.ground, f.commutes]
  coordinate := M.coordinate
  distinct := M.distinct
  multiplier := fun j => f (M.multiplier j)
  multiplierUnit j := (M.multiplierUnit j).map f.toRingHom
  equation j := by
    rw [M.equation j, map_mul]
    cases M.coordinate j <;> simp

def Etale.BoundaryModel.Construction.EtaleBoundaryModel.mulUnits (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w)
    (u : ι → R) (hu : ∀ j, IsUnit (u j)) :
    Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι (fun j => u j * w j) where
  indices := M.indices
  finite := M.finite
  decidableEq := M.decidableEq
  map := M.map
  etale := M.etale
  ground := M.ground
  coordinate := M.coordinate
  distinct := M.distinct
  multiplier := fun j => u j * M.multiplier j
  multiplierUnit j := (hu j).mul (M.multiplierUnit j)
  equation j := by rw [M.equation j, mul_assoc]

def Etale.BoundaryModel.Construction.EtaleBoundaryModel.adjoinUnit (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w)
    (c : R) (hc : IsUnit c) :
    Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R (Option ι) (fun j => match j with | none => c | some i => w i) where
  indices := M.indices
  finite := M.finite
  decidableEq := M.decidableEq
  map := M.map
  etale := M.etale
  ground := M.ground
  coordinate := fun j => match j with | none => none | some i => M.coordinate i
  distinct i j s hi hj := by
    cases i with
    | none => cases hi
    | some i =>
        cases j with
        | none => cases hj
        | some j => exact congrArg some (M.distinct i j s hi hj)
  multiplier := fun j => match j with | none => c | some i => M.multiplier i
  multiplierUnit j := by
    cases j with
    | none => exact hc
    | some i => exact M.multiplierUnit i
  equation j := by
    cases j with
    | none => exact (mul_one c).symm
    | some i => exact M.equation i

end

end OAI.AlgebraicGeometry.Resolution.Blowups
