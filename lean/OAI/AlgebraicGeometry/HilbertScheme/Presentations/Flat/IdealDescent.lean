import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.TensorUnitKernel
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Ideal Descent -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.IdealDescent

noncomputable section

/-! An ideal with matching extensions to the two projections of a flat
cover descends to its contraction on the base. -/

open TensorProduct

universe u v
variable (R : Type u) [CommRing R]
variable (B : Type v) [CommRing B] [Algebra R B] [Module.Flat R B]

theorem flat_ideal_descent (J : Ideal B)
    (hJ : J.map (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B) ≤
      J.map (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B)) :
    (J.comap (algebraMap R B)).map (algebraMap R B) = J := by
  apply le_antisymm Ideal.map_comap_le
  intro b hb
  let q : B →ₐ[R] B ⧸ J := Ideal.Quotient.mkₐ R J
  have hq : RingHom.ker q = J := Ideal.Quotient.mkₐ_ker R J
  have ht : b ⊗ₜ[R] (1 : B) ∈
      RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R B) q) := by
    rw [Algebra.TensorProduct.lTensor_ker q (Ideal.Quotient.mkₐ_surjective R J), hq]
    exact hJ (Ideal.mem_map_of_mem
      (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B) hb)
  have hz : b ∈ RingHom.ker
      (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] (B ⧸ J)) := by
    change b ⊗ₜ[R] (1 : B ⧸ J) = 0
    change (Algebra.TensorProduct.map (AlgHom.id R B) q) (b ⊗ₜ[R] (1 : B)) = 0 at ht
    simpa only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one] using ht
  have hk : RingHom.ker (algebraMap R (B ⧸ J)) = J.comap (algebraMap R B) := by
    ext r
    change algebraMap R (B ⧸ J) r = 0 ↔ algebraMap R B r ∈ J
    rw [IsScalarTower.algebraMap_apply R B (B ⧸ J)]
    exact Ideal.Quotient.eq_zero_iff_mem
  rw [TensorUnitKernel.flat_tensor_unit_kernel R B (B ⧸ J), hk] at hz
  exact hz

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.IdealDescent
