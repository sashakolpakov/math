import OAI.NumberTheory.ArithmeticGroups.Lattices.NilSubmoduleUnipotentGroup
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Topology.Algebra.Group.Units

/-! # Nil Submodule Affine Homeomorphism -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.NilSubmoduleAffineHomeomorphism.Construction

noncomputable section

/-! Subtracting the identity identifies the unit group associated
to a nilpotent submodule with the submodule itself. -/

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def nilSubmoduleAddOne (W : Submodule ℝ A)
    (hmul : ∀ x ∈ W, ∀ y ∈ W, x * y ∈ W) (hnil : ∀ x ∈ W, IsNilpotent x)
    (X : W) : NilSubmoduleUnipotentGroup.Construction.unipotentSubgroupOfNilSubmodule W hmul hnil :=
  ⟨(hnil X.val X.property).isUnit_one_add.unit, by
    change (hnil X.val X.property).isUnit_one_add.unit.val - 1 ∈ W
    rw [(hnil X.val X.property).isUnit_one_add.unit_spec]
    simpa only [add_sub_cancel_left] using X.property⟩

theorem nilSubmoduleAddOne_val (W : Submodule ℝ A)
    (hmul : ∀ x ∈ W, ∀ y ∈ W, x * y ∈ W) (hnil : ∀ x ∈ W, IsNilpotent x)
    (X : W) : (nilSubmoduleAddOne W hmul hnil X).val.val = 1 + X.val :=
  (hnil X.val X.property).isUnit_one_add.unit_spec

def nilSubmoduleAffineHomeomorph [CompleteSpace A] (W : Submodule ℝ A)
    (hmul : ∀ x ∈ W, ∀ y ∈ W, x * y ∈ W) (hnil : ∀ x ∈ W, IsNilpotent x) :
    W ≃ₜ NilSubmoduleUnipotentGroup.Construction.unipotentSubgroupOfNilSubmodule W hmul hnil where
  toFun := nilSubmoduleAddOne W hmul hnil
  invFun g := ⟨g.val.val - 1, g.property⟩
  left_inv X := by
    apply Subtype.ext
    change (nilSubmoduleAddOne W hmul hnil X).val.val - 1 = X.val
    rw [nilSubmoduleAddOne_val, add_sub_cancel_left]
  right_inv g := by
    apply Subtype.ext
    apply Units.ext
    change (nilSubmoduleAddOne W hmul hnil ⟨g.val.val - 1, g.property⟩).val.val = g.val.val
    rw [nilSubmoduleAddOne_val]
    change 1 + (g.val.val - 1) = g.val.val
    abel
  continuous_toFun := by
    have h : Continuous (fun X : W => (nilSubmoduleAddOne W hmul hnil X).val) := by
      apply Units.isOpenEmbedding_val.isEmbedding.continuous_iff.mpr
      change Continuous (fun X : W => (nilSubmoduleAddOne W hmul hnil X).val.val)
      simp_rw [nilSubmoduleAddOne_val]
      exact continuous_const.add continuous_subtype_val
    exact h.subtype_mk _
  continuous_invFun :=
    ((Units.continuous_val.comp continuous_subtype_val).sub continuous_const).subtype_mk _

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.NilSubmoduleAffineHomeomorphism.Construction
