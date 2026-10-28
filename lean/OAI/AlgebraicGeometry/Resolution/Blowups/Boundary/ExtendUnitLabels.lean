import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.BoundaryModel

/-! # Extend Unit Labels -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Restore inactive original boundary labels as the actual invertible equations. -/

universe u v

variable {k R : Type u} {ι : Type v} [CommRing k] [CommRing R] [Algebra k R]
  (w : ι → R) (B : Finset ι)

/-- A model for the selected equations extends to the original family
when every omitted equation is invertible. The omitted labels are
retained as unit components, with their actual equations. -/
def Etale.BoundaryModel.Construction.EtaleBoundaryModel.extendUnitLabels
    (M : Etale.BoundaryModel.Construction.EtaleBoundaryModel k R B (fun j => w j.val))
    (hu : ∀ j, j ∉ B → IsUnit (w j)) : Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w := by
  classical
  refine
    { indices := M.indices
      finite := M.finite
      decidableEq := M.decidableEq
      map := M.map
      etale := M.etale
      ground := M.ground
      coordinate := fun j => if hj : j ∈ B then M.coordinate ⟨j, hj⟩ else none
      distinct := ?_
      multiplier := fun j => if hj : j ∈ B then M.multiplier ⟨j, hj⟩ else w j
      multiplierUnit := ?_
      equation := ?_ }
  · intro i j s hi hj
    by_cases hbi : i ∈ B
    · by_cases hbj : j ∈ B
      · rw [dite_eq_left hbi] at hi
        rw [dite_eq_left hbj] at hj
        exact congrArg Subtype.val (M.distinct ⟨i, hbi⟩ ⟨j, hbj⟩ s hi hj)
      · rw [dite_eq_right hbj] at hj
        cases hj
    · rw [dite_eq_right hbi] at hi
      cases hi
  · intro j
    by_cases hj : j ∈ B
    · rw [dite_eq_left hj]
      exact M.multiplierUnit ⟨j, hj⟩
    · rw [dite_eq_right hj]
      exact hu j hj
  · intro j
    by_cases hj : j ∈ B
    · rw [dite_eq_left hj, dite_eq_left hj]
      exact M.equation ⟨j, hj⟩
    · rw [dite_eq_right hj, dite_eq_right hj]
      exact (mul_one (w j)).symm

end

end OAI.AlgebraicGeometry.Resolution.Blowups
