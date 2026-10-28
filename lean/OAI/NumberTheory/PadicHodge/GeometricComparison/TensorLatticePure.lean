import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Tensor Lattice Pure -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.TensorLatticePure.TensorLatticeConjugation

noncomputable section

/-! Pure-tensor intertwining identifies a transported integral operator
with the conjugated rational operator on the original lattice image. -/

open scoped TensorProduct

universe uR uS uM uV uD
variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type uM} {V : Type uV} {D : Type uD} [AddCommGroup M] [Module R M]
  [AddCommGroup V] [Module S V] [AddCommGroup D] [Module S D]
  (c : S ⊗[R] M ≃ₗ[S] V) (d : S ⊗[R] M ≃ₗ[S] D)
  (φ : Module.End S V) (F : Module.End R M)
  (h : ∀ x : M, c (1 ⊗ₜ[R] F x) = φ (c (1 ⊗ₜ[R] x)))

include h in
theorem pure (x : M) : d (1 ⊗ₜ[R] F x) =
    (c.symm.trans d) (φ ((c.symm.trans d).symm (d (1 ⊗ₜ[R] x)))) := by
  change d (1 ⊗ₜ[R] F x) = d (c.symm (φ (c (d.symm (d (1 ⊗ₜ[R] x))))))
  rw [LinearEquiv.symm_apply_apply, ← h x, LinearEquiv.symm_apply_apply]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.TensorLatticePure.TensorLatticeConjugation
