import OAI.NumberTheory.ArithmeticGroups.Lattices.UpperUnitriangularGroup

/-! # Bounded Upper Unipotent Set -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.BoundedUpperUnipotentSet.Construction

noncomputable section

/-! Bounded entries define a compact subset of the full upper
unitriangular matrix group. -/

def boundedUpperUnipotentSet (m : ℕ) (c : ℝ) : Set (UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup m) :=
  {n | ∀ i j, |n.val.val i j| ≤ c}

theorem boundedUpperUnipotentSet_isCompact (m : ℕ) (c : ℝ) :
    IsCompact (boundedUpperUnipotentSet m c) := by
  have he : boundedUpperUnipotentSet m c = Subtype.val ⁻¹'
      {n : (Matrix (Fin m) (Fin m) ℝ)ˣ | UpperUnitriangularMatrices.Construction.IsUpperUnitriangular n.val ∧ ∀ i j, |n.val i j| ≤ c} := by
    ext n
    exact ⟨fun h => ⟨n.property, h⟩, fun h => h.2⟩
  rw [he]
  exact (UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup_isClosed m).isClosedEmbedding_subtypeVal.isCompact_preimage
    (UpperUnitriangularMatrices.Construction.bounded_upper_unitriangular_isCompact m c)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.BoundedUpperUnipotentSet.Construction
