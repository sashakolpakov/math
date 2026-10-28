import Mathlib.LinearAlgebra.Prod

/-! # Submodule Transport -/

namespace OAI.RepresentationTheory.Theta.Geometric.Normalized.SubmoduleTransport

/-! Equal normalized subspaces are carried exactly by a linear map
intertwining the two normalizers. -/

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

theorem normalizedSubmodule_transport (P Q : Submodule k V) (eA eB f : V ≃ₗ[k] V)
    (hf : ∀ v, f (eA v) = eB v)
    (hPQ : P.map eA.symm.toLinearMap = Q.map eB.symm.toLinearMap) :
    P.map f.toLinearMap = Q := by
  apply Submodule.map_injective_of_injective eB.symm.injective
  rw [← Submodule.map_comp]
  have he : eB.symm.toLinearMap.comp f.toLinearMap = eA.symm.toLinearMap := by
    apply LinearMap.ext
    intro v
    have h := hf (eA.symm v)
    rw [eA.apply_symm_apply] at h
    exact (congrArg eB.symm h).trans (eB.symm_apply_apply (eA.symm v))
  rw [he]
  exact hPQ

end OAI.RepresentationTheory.Theta.Geometric.Normalized.SubmoduleTransport
