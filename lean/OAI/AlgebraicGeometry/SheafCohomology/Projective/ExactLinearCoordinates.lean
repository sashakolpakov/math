import Mathlib.Algebra.Exact.Basic

/-! # Exact Linear Coordinates -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.ExactLinearCoordinates

/-! Exactness transports through commuting linear coordinate equivalences. -/

universe u v₁ v₂ v₃ w₁ w₂ w₃
variable {R : Type u} [CommRing R]
variable {M : Type v₁} {N : Type v₂} {P : Type v₃}
variable {M' : Type w₁} {N' : Type w₂} {P' : Type w₃}
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
variable [AddCommGroup M'] [AddCommGroup N'] [AddCommGroup P']
variable [Module R M] [Module R N] [Module R P]
variable [Module R M'] [Module R N'] [Module R P']

theorem exact_of_linearEquiv_coordinates (eM : M ≃ₗ[R] M') (eN : N ≃ₗ[R] N') (eP : P ≃ₗ[R] P')
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (f' : M' →ₗ[R] N') (g' : N' →ₗ[R] P')
    (hf : ∀ x, eN (f x) = f' (eM x)) (hg : ∀ x, eP (g x) = g' (eN x))
    (hex : Function.Exact f' g') : Function.Exact f g := by
  intro x
  constructor
  · intro hx
    have hx' : g' (eN x) = 0 := by rw [← hg, hx, map_zero]
    obtain ⟨y, hy⟩ := (hex (eN x)).mp hx'
    refine ⟨eM.symm y, eN.injective ?_⟩
    rw [hf, eM.apply_symm_apply, hy]
  · rintro ⟨y, rfl⟩
    apply eP.injective
    rw [map_zero, hg, hf]
    exact hex.apply_apply_eq_zero (eM y)

end OAI.AlgebraicGeometry.SheafCohomology.Projective.ExactLinearCoordinates
