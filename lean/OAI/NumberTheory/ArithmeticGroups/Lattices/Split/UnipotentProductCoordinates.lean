import OAI.NumberTheory.ArithmeticGroups.Lattices.Split.FilteredSection
import OAI.NumberTheory.ArithmeticGroups.Lattices.Split.ExtensionCoordinates

/-! # Unipotent Product Coordinates -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! The split filtered subgroup is homeomorphic to the product
of its split exponential and unipotent subgroups. -/

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L}

def KillingSplit.Construction.KillingSplitWeightData.unipotentKernelHomeomorph (d : KillingSplit.Construction.KillingSplitWeightData B) :
    (Split.FilteredProjection.Construction.splitFilteredProjection B d.basis.toBasis (fun i => d.weight i d.regularElement) d.subspace d.commute).ker ≃ₜ
      UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement) where
  toFun x := ⟨x.val.val, (Split.FilteredProjection.Construction.splitFilteredProjection_eq_one_iff B d.basis (fun i => d.weight i d.regularElement)
    d.subspace d.commute x.val).mp x.property⟩
  invFun n := ⟨⟨n.val, Split.FilteredFactorInclusions.Construction.unipotentBracketUnitGroup_le_splitFiltered B d.basis
    (fun i => d.weight i d.regularElement) d.subspace d.commute n.property⟩,
    (Split.FilteredProjection.Construction.splitFilteredProjection_eq_one_iff B d.basis (fun i => d.weight i d.regularElement)
      d.subspace d.commute _).mpr n.property⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv n := by apply Subtype.ext; rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

def KillingSplit.Construction.KillingSplitWeightData.splitUnipotentHomeomorph (d : KillingSplit.Construction.KillingSplitWeightData B) :
    (CommutingExponentialSubgroup.Construction.commutingExponentialSubgroup d.subspace d.commute) ×
      (UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement)) ≃ₜ
        Split.FilteredBracketGroup.Construction.splitFilteredBracketUnitGroup B d.basis.toBasis (fun i => d.weight i d.regularElement) d.subspace d.commute :=
  ((Homeomorph.refl _).prodCongr d.unipotentKernelHomeomorph.symm).trans
    (Split.ExtensionCoordinates.Construction.splitExtensionHomeomorph
      (Split.FilteredProjection.Construction.splitFilteredProjection B d.basis.toBasis (fun i => d.weight i d.regularElement) d.subspace d.commute)
      d.splitSection (Split.FilteredProjection.Construction.splitFilteredProjection_continuous _ _ _ _ _) d.splitSection_continuous
      d.splitSection_rightInverse)

theorem KillingSplit.Construction.KillingSplitWeightData.splitUnipotentHomeomorph_val
    (d : KillingSplit.Construction.KillingSplitWeightData B)
    (x : (CommutingExponentialSubgroup.Construction.commutingExponentialSubgroup d.subspace d.commute) ×
      (UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement))) :
    (d.splitUnipotentHomeomorph x).val = x.1.val * x.2.val := rfl

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
