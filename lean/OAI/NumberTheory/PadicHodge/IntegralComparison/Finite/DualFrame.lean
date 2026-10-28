import Mathlib.LinearAlgebra.Contraction

/-! # Dual Frame -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.DualFrame

noncomputable section

/-! A finite projective module has an actual finite dual frame. -/

open scoped TensorProduct

universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]

structure Frame (ι : Type u) [Fintype ι] where
  vector : ι → M
  coord : ι → M →ₗ[R] R
  reconstruct : ∀ m, ∑ i, coord i m • vector i = m

variable [Module.Finite R M] [Module.Projective R M]

theorem exists_frame : ∃ (ι : Type u) (_ : Fintype ι), Nonempty (Frame R M ι) := by
  classical
  let t := (dualTensorHomEquiv R M M).symm (LinearMap.id : M →ₗ[R] M)
  obtain ⟨s, hs⟩ := TensorProduct.exists_finset t
  refine ⟨s, inferInstance, ⟨⟨(fun i => i.val.2), (fun i => i.val.1), ?_⟩⟩⟩
  intro m
  have h := congrArg (fun z => dualTensorHom R M M z m) hs
  have ht : dualTensorHom R M M t m = m := by
    exact congrArg (fun f : M →ₗ[R] M => f m) ((dualTensorHomEquiv R M M).apply_symm_apply _)
  rw [ht] at h
  simpa only [map_sum, LinearMap.sum_apply, dualTensorHom_apply, ← s.sum_coe_sort] using h.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.DualFrame
