import OAI.NumberTheory.Quaternion.Arithmetic.PrimeField

/-! # Tangent Scalar Equivalence -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.TangentScalarEquivalence

noncomputable section

/-! Replacing a scalar field by an isomorphic scalar field does not
change tangent directions or their linear span. -/

open Set Filter _root_.Topology

variable {κ κ' E : Type*} [Field κ] [Field κ'] [Algebra κ κ']
  [AddCommGroup E] [Module κ E] [Module κ' E] [IsScalarTower κ κ' E]

theorem span_eq_restrictScalars_of_surjective
    (hsurj : Function.Surjective (algebraMap κ κ')) (s : Set E) :
    Submodule.span κ s = (Submodule.span κ' s).restrictScalars κ := by
  apply le_antisymm (Submodule.span_le_restrictScalars κ κ' s)
  intro x hx
  change x ∈ Submodule.span κ' s at hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact (Submodule.span κ s).zero_mem
  | add x y _ _ hx hy => exact (Submodule.span κ s).add_mem hx hy
  | smul a x _ hx =>
    obtain ⟨b, rfl⟩ := hsurj a
    simpa only [IsScalarTower.algebraMap_smul] using (Submodule.span κ s).smul_mem b hx

variable [TopologicalSpace E]

theorem tangentCone_eq_of_scalar_surjective
    (hsurj : Function.Surjective (algebraMap κ κ')) (s : Set E) (x : E) :
    tangentConeAt κ s x = tangentConeAt κ' s x := by
  apply Subset.antisymm tangentConeAt_mono_field
  intro y hy
  obtain ⟨α, l, hl, c, d, hd, hds, hcd⟩ := exists_fun_of_mem_tangentConeAt hy
  choose b hb using fun a => hsurj (c a)
  apply mem_tangentConeAt_of_seq l b d hd hds
  have he : (fun a => b a • d a) = (fun a => c a • d a) := by
    funext a
    rw [← IsScalarTower.algebraMap_smul κ', hb]
  rwa [he]

theorem tangentSpan_eq_restrictScalars_of_surjective
    (hsurj : Function.Surjective (algebraMap κ κ')) (s : Set E) (x : E) :
    Submodule.span κ (tangentConeAt κ s x) =
      (Submodule.span κ' (tangentConeAt κ' s x)).restrictScalars κ := by
  rw [tangentCone_eq_of_scalar_surjective hsurj, span_eq_restrictScalars_of_surjective hsurj]

end

end OAI.NumberTheory.Quaternion.Arithmetic.TangentScalarEquivalence
