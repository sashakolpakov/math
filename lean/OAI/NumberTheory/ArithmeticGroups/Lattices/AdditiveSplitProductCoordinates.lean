import OAI.NumberTheory.ArithmeticGroups.Lattices.Split.FilteredExponentialCoordinates
import OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.SplitConjugation

/-! # Additive Split Product Coordinates -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! The split filtered group in additive split and unipotent group
coordinates, with the conjugation identity needed for its Haar density. -/

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L}

def KillingSplit.Construction.KillingSplitWeightData.additiveSplitHom (d : KillingSplit.Construction.KillingSplitWeightData B) :
    Multiplicative d.subspace →*
      Split.FilteredBracketGroup.Construction.splitFilteredBracketUnitGroup B d.basis.toBasis (fun i => d.weight i d.regularElement) d.subspace d.commute :=
  d.splitSection.comp (CommutingExponentialSubgroup.Construction.commutingExponentialHom d.subspace d.commute).rangeRestrict

def KillingSplit.Construction.KillingSplitWeightData.unipotentSplitHom (d : KillingSplit.Construction.KillingSplitWeightData B) :
    UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement) →*
      Split.FilteredBracketGroup.Construction.splitFilteredBracketUnitGroup B d.basis.toBasis (fun i => d.weight i d.regularElement) d.subspace d.commute :=
  Subgroup.inclusion (Split.FilteredFactorInclusions.Construction.unipotentBracketUnitGroup_le_splitFiltered B d.basis
    (fun i => d.weight i d.regularElement) d.subspace d.commute)

def KillingSplit.Construction.KillingSplitWeightData.additiveSplitProductHomeomorph (d : KillingSplit.Construction.KillingSplitWeightData B) :
    Multiplicative d.subspace × UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement) ≃ₜ
      Split.FilteredBracketGroup.Construction.splitFilteredBracketUnitGroup B d.basis.toBasis (fun i => d.weight i d.regularElement) d.subspace d.commute :=
  ((CommutingExponentialHomeomorph.Construction.commutingExponentialHomeomorph d.subspace (fun _ hX => (d.le_symmetric hX).1) d.commute).prodCongr
    (Homeomorph.refl _)).trans d.splitUnipotentHomeomorph

theorem KillingSplit.Construction.KillingSplitWeightData.additiveSplitProductHomeomorph_mul (d : KillingSplit.Construction.KillingSplitWeightData B)
    (x : Multiplicative d.subspace × UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement)) :
    d.additiveSplitProductHomeomorph x = d.additiveSplitHom x.1 * d.unipotentSplitHom x.2 := by
  apply Subtype.ext
  rfl

theorem KillingSplit.Construction.KillingSplitWeightData.additiveSplitProduct_conjugation (d : KillingSplit.Construction.KillingSplitWeightData B)
    (A : Multiplicative d.subspace)
    (n : UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement)) :
    d.unipotentSplitHom (d.unipotentConjugation (-A.toAdd) n) =
      (d.additiveSplitHom A)⁻¹ * d.unipotentSplitHom n * d.additiveSplitHom A := by
  apply Subtype.ext
  apply Units.ext
  change (d.unipotentConjugation (-A.toAdd) n).val.val =
    NormedSpace.exp (-A.toAdd.val) * n.val.val * NormedSpace.exp A.toAdd.val
  simpa only [Submodule.coe_neg, neg_neg] using d.unipotentConjugation_val (-A.toAdd) n

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
