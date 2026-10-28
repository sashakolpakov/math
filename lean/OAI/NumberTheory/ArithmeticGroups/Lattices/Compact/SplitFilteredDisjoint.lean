import OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalFilteredProjection
import OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalSymmetricExponential
import OAI.NumberTheory.ArithmeticGroups.Lattices.Split.FilteredBracketGroup

/-! # Split Filtered Disjoint -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.SplitFilteredDisjoint.Construction

noncomputable section

/-! The compact orthogonal factor and the closed split filtered
factor intersect only in the identity. -/

theorem orthogonal_splitFiltered_inf_eq_bot
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (B : L →L[ℝ] L →L[ℝ] L) (b : OrthonormalBasis (Fin m) ℝ L) (w : Fin m → ℝ)
    (a : Submodule ℝ (L →L[ℝ] L)) (ha : ∀ X ∈ a, X.toLinearMap.IsSymmetric)
    (hc : ∀ X ∈ a, ∀ Y ∈ a, Commute X Y) :
    OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnitGroup B ⊓ Split.FilteredBracketGroup.Construction.splitFilteredBracketUnitGroup B b.toBasis w a hc = ⊥ := by
  apply le_antisymm _ bot_le
  intro g hg
  obtain ⟨_, hF, hproj⟩ := (Split.FilteredBracketGroup.Construction.mem_splitFilteredBracketUnitGroup_iff B b.toBasis w a hc g).mp hg.2
  rw [OrthogonalFilteredProjection.Construction.orthogonal_filtered_operator_projection_eq B b w g hg.1 hF] at hproj
  obtain ⟨X, hX⟩ := hproj
  change OperatorExponentialUnits.Construction.operatorExpUnit X.toAdd.val = g at hX
  have hk : OperatorExponentialUnits.Construction.operatorExpUnit X.toAdd.val ∈ OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnitGroup B := hX.symm ▸ hg.1
  have hzero := OrthogonalSymmetricExponential.Construction.symmetric_exponential_orthogonal_eq_zero X.toAdd.val
    (ha X.toAdd.val X.toAdd.property) hk.2
  change g = 1
  rw [← hX, hzero, OperatorExponentialUnits.Construction.operatorExpUnit_zero]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.SplitFilteredDisjoint.Construction
