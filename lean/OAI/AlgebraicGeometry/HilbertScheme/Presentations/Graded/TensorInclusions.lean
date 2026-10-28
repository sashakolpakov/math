import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.LinearAlgebra.TensorProduct.Map

/-! # Tensor Inclusions -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.TensorInclusions.GradedModules

noncomputable section

/-! A homogeneous component is a split submodule, so its inclusion stays injective after tensoring. -/

open DirectSum

universe u v w t

variable {R : Type u} [CommRing R] {δ : Type v} [DecidableEq δ]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable (ℳ : δ → Submodule R M) [Decomposition ℳ]

def homogeneousComponentProjection (d : δ) : M →ₗ[R] ℳ d :=
  (DirectSum.component R δ (fun i => ℳ i) d).comp (decomposeLinearEquiv ℳ).toLinearMap

theorem homogeneousComponentProjection_subtype (d : δ) :
    (homogeneousComponentProjection ℳ d).comp (ℳ d).subtype = LinearMap.id := by
  apply LinearMap.ext
  intro m
  apply Subtype.ext
  exact decompose_of_mem_same ℳ m.property

theorem homogeneousSubtype_lTensor_injective (d : δ)
    (S : Type t) [AddCommGroup S] [Module R S] :
    Function.Injective ((ℳ d).subtype.lTensor S) := by
  have h : ((homogeneousComponentProjection ℳ d).lTensor S).comp ((ℳ d).subtype.lTensor S) =
      LinearMap.id := by
    rw [← LinearMap.lTensor_comp, homogeneousComponentProjection_subtype, LinearMap.lTensor_id]
  intro x y hxy
  have he := congrArg ((homogeneousComponentProjection ℳ d).lTensor S) hxy
  exact (DFunLike.congr_fun h x).symm.trans (he.trans (DFunLike.congr_fun h y))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.TensorInclusions.GradedModules
