import Mathlib.LinearAlgebra.Isomorphisms

/-! # Surjective Linear Coordinates -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.SurjectiveLinearCoordinates

noncomputable section

/-! Two surjective linear maps with equal kernels give compatible target coordinates. -/

universe u v w t
variable {R : Type u} [Ring R]
variable {M : Type v} {N : Type w} {P : Type t}
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
variable [Module R M] [Module R N] [Module R P]

def surjectiveLinearCoordinates (f : M →ₗ[R] N) (g : M →ₗ[R] P)
    (hf : Function.Surjective f) (hg : Function.Surjective g) (hk : f.ker = g.ker) : N ≃ₗ[R] P :=
  (f.quotKerEquivOfSurjective hf).symm.trans
    ((Submodule.quotEquivOfEq _ _ hk).trans (g.quotKerEquivOfSurjective hg))

theorem surjectiveLinearCoordinates_apply (f : M →ₗ[R] N) (g : M →ₗ[R] P)
    (hf : Function.Surjective f) (hg : Function.Surjective g) (hk : f.ker = g.ker) (x : M) :
    surjectiveLinearCoordinates f g hf hg hk (f x) = g x := by
  simp only [surjectiveLinearCoordinates, LinearEquiv.trans_apply,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.SurjectiveLinearCoordinates
