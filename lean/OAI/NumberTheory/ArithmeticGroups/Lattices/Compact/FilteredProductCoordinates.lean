import OAI.NumberTheory.ArithmeticGroups.Lattices.RelativeSubgroupProductCoordinates
import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.SplitFilteredDisjoint
import OAI.NumberTheory.ArithmeticGroups.Lattices.WeightedGlobalIwasawa

/-! # Filtered Product Coordinates -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! Global topological product coordinates for the compact and
split filtered factors of an adjoint-stable bracket automorphism group. -/

open _root_.ContinuousLinearMap

theorem KillingSplit.Construction.KillingSplitWeightData.compact_filtered_product_isHomeomorph
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {B : L →L[ℝ] L →L[ℝ] L} (d : KillingSplit.Construction.KillingSplitWeightData B)
    (hadj : ∀ g : L ≃L[ℝ] L, ContinuousBracketChange.Construction.continuousBracketChange g B = B →
      ∀ x y, adjoint g.toContinuousLinearMap (B x y) =
        B (adjoint g.toContinuousLinearMap x) (adjoint g.toContinuousLinearMap y))
    (hDadj : ∀ X, Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B X = 0 →
      Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B (adjoint X) = 0) :
    IsHomeomorph (fun x :
      ((OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnitGroup B).comap (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B).subtype) ×
      ((Split.FilteredBracketGroup.Construction.splitFilteredBracketUnitGroup B d.basis.toBasis (fun i => d.weight i d.regularElement)
        d.subspace d.commute).comap (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B).subtype) => x.1.val * x.2.val) := by
  apply RelativeSubgroupProductCoordinates.Construction.relative_compact_closed_product_isHomeomorph (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B)
    (OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnitGroup B)
    (Split.FilteredBracketGroup.Construction.splitFilteredBracketUnitGroup B d.basis.toBasis (fun i => d.weight i d.regularElement) d.subspace d.commute)
    (UnipotentBracketGroup.Construction.continuousBracketUnitGroup_isClosed B) (OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnitGroup_isCompact B)
    (Split.FilteredBracketGroup.Construction.splitFilteredBracketUnitGroup_isClosed B d.basis.toBasis (fun i => d.weight i d.regularElement)
      d.subspace (fun X hX => (d.le_symmetric hX).1) d.commute)
    (fun _ hg => hg.1) (fun _ hg => hg.1)
    (Compact.SplitFilteredDisjoint.Construction.orthogonal_splitFiltered_inf_eq_bot B d.basis (fun i => d.weight i d.regularElement)
      d.subspace (fun X hX => (d.le_symmetric hX).1) d.commute)
  intro g hg
  exact GlobalSplitFilteredProduct.Construction.bracket_global_splitFiltered_product B hadj d.subspace d.regularElement.val d.le_symmetric d.commute
    d.regularElement.property (d.linear_iwasawa hDadj) d.basis (fun i => d.weight i d.regularElement)
    (fun i => d.eigenvector i d.regularElement) g hg

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
