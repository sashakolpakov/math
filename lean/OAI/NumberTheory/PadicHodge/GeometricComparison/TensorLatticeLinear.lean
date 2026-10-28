import OAI.NumberTheory.PadicHodge.GeometricComparison.TensorLatticePure

/-! # Tensor Lattice Linear -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.TensorLatticeLinear.TensorLatticeIntertwining

noncomputable section

/-! A rational tensor-intertwining identity descends to an equality
of integral lattice maps under the actual generic-fiber inclusion. -/

open scoped TensorProduct

universe uR uS uM uV uD
variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type uM} {V : Type uV} {D : Type uD} [AddCommGroup M] [Module R M]
  [AddCommGroup V] [Module S V] [AddCommGroup D] [Module S D]
  [Module R D] [IsScalarTower R S D]
  (c : S ⊗[R] M ≃ₗ[S] V) (d : S ⊗[R] M ≃ₗ[S] D)
  (φ : Module.End S V) (F : Module.End R M)
  (h : c.toLinearMap.comp (F.baseChange S) = φ.comp c.toLinearMap)

def inclusion : M →ₗ[R] D :=
  (d.toLinearMap.restrictScalars R).comp (TensorProduct.mk R S M 1)

def conjugate : Module.End S D :=
  (c.symm.trans d).toLinearMap.comp (φ.comp (c.symm.trans d).symm.toLinearMap)

include h in
theorem linearMap : (inclusion d).comp F = ((conjugate c d φ).restrictScalars R).comp (inclusion d) := by
  apply LinearMap.ext
  intro x
  exact TensorLatticePure.TensorLatticeConjugation.pure c d φ F
    (fun y => LinearMap.congr_fun h (1 ⊗ₜ[R] y)) x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.TensorLatticeLinear.TensorLatticeIntertwining
