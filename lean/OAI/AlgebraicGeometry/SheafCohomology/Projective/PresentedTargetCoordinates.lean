import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.Exact.Basic

/-! # Presented Target Coordinates -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.PresentedTargetCoordinates

noncomputable section

/-! Changing coordinates in a genuine linear presentation preserves its presented target. -/

universe u v w t v' w'
variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable {P : Type t} [AddCommGroup P] [Module R P]
variable {M' : Type v'} [AddCommGroup M'] [Module R M']
variable {N' : Type w'} [AddCommGroup N'] [Module R N']

abbrev LinearCokernel (f : M →ₗ[R] N) := N ⧸ f.range

def presentationCoordinateMap (f : M →ₗ[R] N) (eM : M ≃ₗ[R] M') (eN : N ≃ₗ[R] N') :
    M' →ₗ[R] N' := eN.toLinearMap.comp (f.comp eM.symm.toLinearMap)

theorem presentationCoordinateMap_exact (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hex : Function.Exact f g) (eM : M ≃ₗ[R] M') (eN : N ≃ₗ[R] N') :
    Function.Exact (presentationCoordinateMap f eM eN) (g.comp eN.symm.toLinearMap) := by
  intro n
  constructor
  · intro hn
    obtain ⟨m, hm⟩ := (hex (eN.symm n)).mp hn
    refine ⟨eM m, ?_⟩
    change eN (f (eM.symm (eM m))) = n
    rw [eM.symm_apply_apply, hm, eN.apply_symm_apply]
  · rintro ⟨m, hm⟩
    change g (eN.symm n) = 0
    apply (hex (eN.symm n)).mpr
    refine ⟨eM.symm m, ?_⟩
    apply eN.injective
    exact hm.trans (eN.apply_symm_apply n).symm

def presentedTargetCoordinatesEquiv (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hex : Function.Exact f g) (hs : Function.Surjective g)
    (eM : M ≃ₗ[R] M') (eN : N ≃ₗ[R] N') :
    (N' ⧸ (presentationCoordinateMap f eM eN).range) ≃ₗ[R] P := by
  let g' := g.comp eN.symm.toLinearMap
  have heq : (presentationCoordinateMap f eM eN).range = g'.ker :=
    (LinearMap.exact_iff.mp (presentationCoordinateMap_exact f g hex eM eN)).symm
  exact (Submodule.quotEquivOfEq _ _ heq).trans
    (g'.quotKerEquivOfSurjective (hs.comp eN.symm.surjective))

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.PresentedTargetCoordinates
