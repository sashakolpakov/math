import Mathlib.RingTheory.HopfAlgebra.Convolution

/-! # Twisted Group Like Unit -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.TwistedGroupLikeUnit

/-! A normalized group-like element for a unit twist is invertible in the original Hopf algebra. -/

universe u v

open Coalgebra HopfAlgebra TensorProduct

variable (k : Type u) (R : Type v) [CommRing k] [CommRing R] [HopfAlgebra k R]

/-- Multiplication after applying the antipode to the second factor is an algebra map. -/
noncomputable def contraction : R ⊗[k] R →ₐ[k] R :=
  Algebra.TensorProduct.lift (.id k R) (antipodeAlgHom k R) (fun _ _ ↦ Commute.all _ _)

@[simp]
theorem contraction_tmul (a b : R) : contraction k R (a ⊗ₜ b) = a * antipode k b := rfl

/-- The antipode identity evaluated by this contraction. -/
theorem contraction_comul (a : R) :
    contraction k R (comul a) = algebraMap k R (counit a) := by
  have h : (contraction k R).toLinearMap =
      (LinearMap.mul' k R).comp ((antipode k).lTensor R) := by
    ext a b
    rfl
  change (contraction k R).toLinearMap (comul a) = _
  rw [h]
  exact mul_antipode_lTensor_comul_apply a

/-- This works for infinitesimal finite group schemes as well as reduced ones. -/
theorem isUnit_of_twisted_groupLike (c : (R ⊗[k] R)ˣ) (a : R)
    (hε : counit (R := k) a = 1) (hΔ : (c : R ⊗[k] R) * comul a = a ⊗ₜ[k] a) :
    IsUnit a := by
  have h := congrArg (contraction k R) hΔ
  rw [map_mul, contraction_comul, hε, map_one, mul_one, contraction_tmul] at h
  have hu : IsUnit (a * antipode k a) := h ▸ c.isUnit.map (contraction k R)
  exact isUnit_of_mul_isUnit_left hu

end OAI.AlgebraicGeometry.Picard.PoincareBundle.TwistedGroupLikeUnit
