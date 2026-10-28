import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.QuotientLattice

/-! # Locally Compact Group Polish -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.LocallyCompactGroupPolish.Construction

noncomputable section

/-! A second countable locally compact Hausdorff group is Polish. -/

theorem locallyCompact_group_polish
    (H : Type*) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H] : PolishSpace H := by
  let : UniformSpace H := IsTopologicalGroup.rightUniformSpace H
  let : IsRightUniformGroup H := ⟨rfl⟩
  let : CompleteSpace H := IsRightUniformGroup.completeSpace_of_weaklyLocallyCompactSpace H
  let : (uniformity H).IsCountablyGenerated := Filter.comap.isCountablyGenerated _ _
  infer_instance

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.LocallyCompactGroupPolish.Construction
