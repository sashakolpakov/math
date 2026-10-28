import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.ExtendUnitLabels

/-! # Unit Labels Unused -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Restoring unit labels preserves an unused normal coordinate. -/

universe u v

theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.extendUnitLabels_unused
    {k R : Type u} {ι : Type v} [CommRing k] [CommRing R] [Algebra k R]
    (w : ι → R) (B : Finset ι) (M : Etale.BoundaryModel.Construction.EtaleBoundaryModel k R B (fun j => w j.val))
    (hu : ∀ j, j ∉ B → IsUnit (w j)) (h : M.indices)
    (hh : ∀ j, M.coordinate j ≠ some h) (j : ι) :
    (M.extendUnitLabels w B hu).coordinate j ≠ some h := by
  classical
  change (if hj : j ∈ B then M.coordinate ⟨j, hj⟩ else none) ≠ some h
  by_cases hj : j ∈ B
  · rw [dite_eq_left hj]
    exact hh ⟨j, hj⟩
  · rw [dite_eq_right hj]
    intro hbad
    cases hbad

end

end OAI.AlgebraicGeometry.Resolution.Blowups
