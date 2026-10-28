import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Module.Basic

/-! # Invariant Submodule Equivalence -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantSubmoduleEquivalence.Construction

noncomputable section

/-! Restriction of a continuous linear equivalence to an invariant
subspace, retaining its inverse and topology. -/

def invariantSubmoduleEquiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : E ≃L[ℝ] E) (P : Submodule ℝ E)
    (he : ∀ x ∈ P, e x ∈ P) (hi : ∀ x ∈ P, e.symm x ∈ P) : P ≃L[ℝ] P where
  toFun x := ⟨e x.val, he x.val x.property⟩
  invFun x := ⟨e.symm x.val, hi x.val x.property⟩
  left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x.val
  right_inv x := by apply Subtype.ext; exact e.apply_symm_apply x.val
  map_add' x y := by apply Subtype.ext; exact e.map_add x.val y.val
  map_smul' c x := by apply Subtype.ext; exact e.map_smul c x.val
  continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _

theorem invariantSubmoduleEquiv_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : E ≃L[ℝ] E) (P : Submodule ℝ E)
    (he : ∀ x ∈ P, e x ∈ P) (hi : ∀ x ∈ P, e.symm x ∈ P) (x : P) :
    (invariantSubmoduleEquiv e P he hi x).val = e x.val := rfl

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantSubmoduleEquivalence.Construction
