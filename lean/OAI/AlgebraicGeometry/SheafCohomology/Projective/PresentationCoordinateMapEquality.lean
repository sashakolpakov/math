import OAI.AlgebraicGeometry.SheafCohomology.Projective.PresentedTargetCoordinates

/-! # Presentation Coordinate Map Equality -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.PresentationCoordinateMapEquality

/-! Check a presentation map in the original source coordinates. -/

universe u v w v' w'
variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable {M' : Type v'} [AddCommGroup M'] [Module R M']
variable {N' : Type w'} [AddCommGroup N'] [Module R N']

theorem presentationCoordinateMap_eq_of (f : M →ₗ[R] N)
    (eM : M ≃ₗ[R] M') (eN : N ≃ₗ[R] N') (p : M' →ₗ[R] N')
    (h : ∀ x, eN (f x) = p (eM x)) : PresentedTargetCoordinates.presentationCoordinateMap f eM eN = p := by
  ext x
  obtain ⟨y, rfl⟩ := eM.surjective x
  change eN (f (eM.symm (eM y))) = p (eM y)
  rw [eM.symm_apply_apply]
  exact h y

end OAI.AlgebraicGeometry.SheafCohomology.Projective.PresentationCoordinateMapEquality
