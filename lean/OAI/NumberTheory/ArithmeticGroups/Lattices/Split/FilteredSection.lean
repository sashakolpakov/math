import OAI.NumberTheory.ArithmeticGroups.Lattices.Split.FilteredProjection
import OAI.NumberTheory.ArithmeticGroups.Lattices.KillingSplit

/-! # Filtered Section -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! The split exponential subgroup is a continuous homomorphic
section of the block projection on the split filtered subgroup. -/

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L}

def KillingSplit.Construction.KillingSplitWeightData.splitSection (d : KillingSplit.Construction.KillingSplitWeightData B) :
    CommutingExponentialSubgroup.Construction.commutingExponentialSubgroup d.subspace d.commute →*
      Split.FilteredBracketGroup.Construction.splitFilteredBracketUnitGroup B d.basis.toBasis (fun i => d.weight i d.regularElement) d.subspace d.commute :=
  Subgroup.inclusion (Split.FilteredFactorInclusions.Construction.commutingExponentialSubgroup_le_splitFiltered B d.basis
    (fun i => d.weight i d.regularElement) d.regularElement.val d.subspace d.le_symmetric d.commute
    d.regularElement.property (fun i => d.eigenvector i d.regularElement))

theorem KillingSplit.Construction.KillingSplitWeightData.splitSection_continuous
    (d : KillingSplit.Construction.KillingSplitWeightData B) : Continuous d.splitSection := continuous_subtype_val.subtype_mk _

theorem KillingSplit.Construction.KillingSplitWeightData.splitSection_rightInverse
    (d : KillingSplit.Construction.KillingSplitWeightData B) (g : CommutingExponentialSubgroup.Construction.commutingExponentialSubgroup d.subspace d.commute) :
    Split.FilteredProjection.Construction.splitFilteredProjection B d.basis.toBasis (fun i => d.weight i d.regularElement)
      d.subspace d.commute (d.splitSection g) = g := by
  have hHg : Commute d.regularElement.val (g.val : L →L[ℝ] L) := by
    obtain ⟨X, hX⟩ := g.property
    rw [← hX]
    exact (d.commute d.regularElement.val d.regularElement.property X.toAdd.val X.toAdd.property).exp_right
  apply Subtype.ext
  exact CommutingFilteredUnits.Construction.commuting_unit_weightBlockProjection_eq d.basis (fun i => d.weight i d.regularElement)
    d.regularElement.val (d.le_symmetric d.regularElement.property).1
    (fun i => d.eigenvector i d.regularElement)
    (Split.FilteredProjection.Construction.splitFilteredToFilteredHom B d.basis.toBasis (fun i => d.weight i d.regularElement)
      d.subspace d.commute (d.splitSection g)) hHg

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
