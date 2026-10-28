import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.LogarithmicCoordinates

/-! # At Prime -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Identify the finite coordinate boundary through a prime containing the actual equations. -/

universe u v

variable {k A : Type u} {ι : Type v} [CommRing k] [CommRing A] [Algebra k A]
  {w : ι → A}

theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.boundary_coordinates_mem (M : Etale.BoundaryModel.Construction.EtaleBoundaryModel k A ι w)
    (q : Ideal A) (hw : ∀ j, w j ∈ q) (s : M.indices) (hs : s ∈ M.boundaryIndices) :
    M.map (MvPolynomial.X s) ∈ q := by
  obtain ⟨j, hj⟩ := (M.mem_boundaryIndices s).mp hs
  have he : w j = M.multiplier j * M.map (MvPolynomial.X s) := by
    simpa only [hj] using M.equation j
  apply (q.unit_mul_mem_iff_mem (M.multiplierUnit j)).mp
  rw [← he]
  exact hw j

end

end OAI.AlgebraicGeometry.Resolution.Blowups
