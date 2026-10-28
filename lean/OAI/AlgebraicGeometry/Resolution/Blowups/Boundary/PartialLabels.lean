import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.Operations

/-! # Partial Labels -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Retain unit labels while pulling back a normal-crossing model along a partial injection of labels. -/

universe u v t

variable {k R : Type u} {ι : Type v} {κ : Type t}
  [CommRing k] [CommRing R] [Algebra k R] {w : κ → R}

/-- A missing target label denotes a unit equation. Distinct present
labels select distinct components of the original model. -/
def Etale.BoundaryModel.Construction.EtaleBoundaryModel.pullbackLabels (M : Etale.BoundaryModel.Construction.EtaleBoundaryModel k R κ w)
    (r : ι → Option κ)
    (hr : ∀ i j s, r i = some s → r j = some s → i = j)
    (v u : ι → R) (hu : ∀ j, IsUnit (u j))
    (hv : ∀ j, v j = u j * (match r j with | none => 1 | some s => w s)) :
    Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι v where
  indices := M.indices
  finite := M.finite
  decidableEq := M.decidableEq
  map := M.map
  etale := M.etale
  ground := M.ground
  coordinate := fun j => (r j).bind M.coordinate
  distinct i j s hi hj := by
    cases hri : r i with
    | none => simp only [hri, Option.bind_none] at hi; cases hi
    | some a =>
        cases hrj : r j with
        | none => simp only [hrj, Option.bind_none] at hj; cases hj
        | some b =>
            have hi' : M.coordinate a = some s := by simpa only [hri, Option.bind_some] using hi
            have hj' : M.coordinate b = some s := by simpa only [hrj, Option.bind_some] using hj
            have hab : b = a := (M.distinct a b s hi' hj').symm
            exact hr i j a hri (hrj.trans (congrArg some hab))
  multiplier := fun j => u j * (match r j with | none => 1 | some s => M.multiplier s)
  multiplierUnit j := by
    cases hrj : r j with
    | none => simpa using hu j
    | some s => exact (hu j).mul (M.multiplierUnit s)
  equation j := by
    rw [hv j]
    cases hrj : r j with
    | none => simp
    | some s =>
        simp only [Option.bind_some]
        rw [M.equation s, mul_assoc]

end

end OAI.AlgebraicGeometry.Resolution.Blowups
