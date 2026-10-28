import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Projection

/-! # Linear Immersion Complement -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.LinearImmersionComplement

noncomputable section

/-!
# A continuous linear normal complement

An injective linear map between finite-dimensional normed vector spaces has a
complement on which addition gives a continuous linear isomorphism. The norm
need not come from an inner product. This supplies the linear part of the
inverse-function construction of local coordinates for a smooth immersion.
-/

variable {K E F : Type*} [RCLike K]
  [NormedAddCommGroup E] [NormedSpace K E] [FiniteDimensional K E]
  [NormedAddCommGroup F] [NormedSpace K F] [FiniteDimensional K F]

/-- Addition along a specified complement to the image of an injective map. -/
def linearImmersionComplementEquiv (L : E →L[K] F) (hL : Function.Injective L)
    (C : Submodule K F) (hC : IsCompl (LinearMap.range L.toLinearMap) C) :
    (E × C) ≃L[K] F :=
  (((LinearEquiv.ofInjective L.toLinearMap hL).prodCongr (LinearEquiv.refl K C)).trans
    (Submodule.prodEquivOfIsCompl (LinearMap.range L.toLinearMap) C hC)).toContinuousLinearEquiv

@[simp]
theorem linearImmersionComplementEquiv_apply (L : E →L[K] F)
    (hL : Function.Injective L) (C : Submodule K F)
    (hC : IsCompl (LinearMap.range L.toLinearMap) C) (z : E × C) :
    linearImmersionComplementEquiv L hL C hC z = L z.1 + (z.2 : F) := rfl

/-- Every finite-dimensional linear immersion admits genuine linear normal
coordinates, with the prescribed map on the first factor. -/
theorem exists_linearImmersionComplement (L : E →L[K] F)
    (hL : Function.Injective L) :
    ∃ (C : Submodule K F) (e : (E × C) ≃L[K] F),
      ∀ z, e z = L z.1 + (z.2 : F) := by
  obtain ⟨C, hC⟩ := (LinearMap.range L.toLinearMap).exists_isCompl
  exact ⟨C, linearImmersionComplementEquiv L hL C hC, fun _ ↦ rfl⟩

@[simp]
theorem linearImmersionComplementEquiv_apply_zero (L : E →L[K] F)
    (hL : Function.Injective L) (C : Submodule K F)
    (hC : IsCompl (LinearMap.range L.toLinearMap) C) (x : E) :
    linearImmersionComplementEquiv L hL C hC (x, 0) = L x := by simp

@[simp]
theorem linearImmersionComplementEquiv_symm_apply (L : E →L[K] F)
    (hL : Function.Injective L) (C : Submodule K F)
    (hC : IsCompl (LinearMap.range L.toLinearMap) C) (x : E) :
    (linearImmersionComplementEquiv L hL C hC).symm (L x) = (x, 0) := by
  apply (linearImmersionComplementEquiv L hL C hC).injective
  simp

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.LinearImmersionComplement
