import OAI.AlgebraicGeometry.Resolution.Blowups.OptionalBoundaryLabels
import OAI.AlgebraicGeometry.Resolution.Blowups.Mixed.CoordinateBoundaryFamily
import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.Equations

/-! # Mixed Boundary Family -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! The canonical mixed family for every represented coordinate of a boundary model. -/

universe u v

variable {k R : Type u} {ι : Type v} [Field k] [CommRing R] [Algebra k R]
  {w : ι → R}

def Etale.BoundaryModel.Construction.EtaleBoundaryModel.mixedCoordinateFamily (M : Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w)
    (C : Finset M.indices) (a : (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map M.map) :
    Option M.boundaryIndices → Blowup.Charts.Construction.blowupChart ((SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map M.map) a :=
  letI : Algebra (MvPolynomial M.indices k) R := M.map.toAlgebra
  Mixed.CoordinateBoundaryFamily.Construction.mixedCoordinateBoundaryFamily C a ⟨Subtype.val, Subtype.val_injective⟩

theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.coordinateCenter_boundary_mem (M : Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w)
    (C : Finset M.indices) (F : Finset ι)
    (hF : ∀ j, j ∈ F ↔ ∃ s ∈ C, M.coordinate j = some s)
    (j : ι) (hj : j ∈ F) : w j ∈ (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map M.map := by
  let : Algebra (MvPolynomial M.indices k) R := M.map.toAlgebra
  obtain ⟨s, hs, hjs⟩ := (hF j).mp hj
  rw [M.equation j, hjs]
  exact ((SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map M.map).mul_mem_left (M.multiplier j)
    (Etale.CoefficientStep.Construction.etaleCoordinateElement (K := k) (S := R) C ⟨s, hs⟩).property

end

end OAI.AlgebraicGeometry.Resolution.Blowups
