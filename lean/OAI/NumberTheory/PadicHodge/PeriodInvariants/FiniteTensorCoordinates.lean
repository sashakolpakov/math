import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-! # Finite Tensor Coordinates -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteTensorCoordinates

noncomputable section

/-!
# Finite coordinates for tensor products and their continuous maps

A basis of the finite free second factor identifies the tensor product
with a finite family of coefficient vectors. Tensor maps then become
finite matrices of continuous linear coefficient maps.
-/

open scoped TensorProduct

variable {R M N E F I J : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def coordinates (b : Module.Basis I R E) : M ⊗[R] E ≃ₗ[R] (I → M) :=
  (TensorProduct.congr (LinearEquiv.refl R M) b.equivFun).trans (TensorProduct.piScalarRight R R M I)

theorem coordinates_tmul (b : Module.Basis I R E) (m : M) (e : E) (i : I) :
    coordinates b (m ⊗ₜ[R] e) i = b.repr e i • m := by
  simp [coordinates, TensorProduct.piScalarRight_apply]

theorem coordinates_symm (b : Module.Basis I R E) (v : I → M) :
    (coordinates b).symm v = ∑ i, v i ⊗ₜ[R] b i := by
  apply (coordinates b).injective
  rw [LinearEquiv.apply_symm_apply, map_sum]
  funext j
  simp [coordinates_tmul, Module.Basis.repr_self, Finsupp.single_apply]

theorem map_coordinates (b : Module.Basis I R E) (c : Module.Basis J R F)
    (f : M →ₗ[R] N) (g : E →ₗ[R] F) (v : I → M) (j : J) :
    coordinates c (TensorProduct.map f g ((coordinates b).symm v)) j =
      ∑ i, c.repr (g (b i)) j • f (v i) := by
  rw [coordinates_symm, map_sum, map_sum]
  simp only [Finset.sum_apply, TensorProduct.map_tmul, coordinates_tmul]

variable [TopologicalSpace R] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul R M]
  [TopologicalSpace N] [IsTopologicalAddGroup N] [ContinuousSMul R N]

def matrixMap (b : Module.Basis I R E) (c : Module.Basis J R F)
    (f : M →L[R] N) (g : E →ₗ[R] F) : (I → M) →L[R] (J → N) :=
  ContinuousLinearMap.pi (fun j => ∑ i, c.repr (g (b i)) j • f.comp (ContinuousLinearMap.proj i))

omit [DecidableEq I] [Fintype J] [DecidableEq J] [IsTopologicalAddGroup M] [ContinuousSMul R M] in
theorem matrixMap_apply (b : Module.Basis I R E) (c : Module.Basis J R F)
    (f : M →L[R] N) (g : E →ₗ[R] F) (v : I → M) (j : J) :
    matrixMap b c f g v j = ∑ i, c.repr (g (b i)) j • f (v i) := by
  simp [matrixMap]

omit [IsTopologicalAddGroup M] [ContinuousSMul R M] in
theorem matrixMap_coordinates (b : Module.Basis I R E) (c : Module.Basis J R F)
    (f : M →L[R] N) (g : E →ₗ[R] F) (z : M ⊗[R] E) :
    matrixMap b c f g (coordinates b z) = coordinates c (TensorProduct.map f.toLinearMap g z) := by
  funext j
  rw [matrixMap_apply]
  have h := map_coordinates b c f.toLinearMap g (coordinates b z) j
  rw [LinearEquiv.symm_apply_apply] at h
  exact h.symm

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteTensorCoordinates
