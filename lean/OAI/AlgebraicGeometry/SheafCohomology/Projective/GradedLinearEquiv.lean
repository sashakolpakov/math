import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.Exactness

/-! # Graded Linear Equiv -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedLinearEquiv

noncomputable section

/-! A homogeneous linear equivalence preserves the grading in both directions. -/

open DirectSum OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.Exactness.GradedModules
universe u v w
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
variable (𝒩 : ℤ → Submodule R N) [Decomposition 𝒩]

theorem gradedLinearEquiv_symm_homogeneous (e : M ≃ₗ[R] N)
    (he : ∀ d x, x ∈ ℳ d → e x ∈ 𝒩 d) (d : ℤ) (y : N) (hy : y ∈ 𝒩 d) :
    e.symm y ∈ ℳ d := by
  have h := HilbertScheme.Presentations.Graded.Exactness.GradedModules.homogeneous_preimage ℳ 𝒩 e.toLinearMap he d y hy
    (e.symm y) (e.apply_symm_apply y)
  have hx : (decompose ℳ (e.symm y) d).val = e.symm y :=
    e.injective (h.trans (e.apply_symm_apply y).symm)
  exact hx ▸ (decompose ℳ (e.symm y) d).property

def gradedLinearEquivOnDegree (e : M ≃ₗ[R] N)
    (he : ∀ d x, x ∈ ℳ d → e x ∈ 𝒩 d) (d : ℤ) : ℳ d ≃ₗ[R] 𝒩 d :=
  LinearEquiv.ofBijective (HilbertScheme.Presentations.Graded.Exactness.GradedModules.degreeMap ℳ 𝒩 e.toLinearMap he d)
    ⟨fun _ _ h => Subtype.ext (e.injective (congrArg Subtype.val h)),
      HilbertScheme.Presentations.Graded.Exactness.GradedModules.degreeMap_surjective ℳ 𝒩 e.toLinearMap he e.surjective d⟩

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedLinearEquiv
