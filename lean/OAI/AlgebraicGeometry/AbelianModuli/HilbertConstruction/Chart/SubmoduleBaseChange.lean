import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.ChartBaseChange

/-! # Submodule Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chart.SubmoduleBaseChange

noncomputable section

/-! Scalar extension commutes with inverse image under compatible ambient isomorphisms. -/

universe u v w t

variable {R : Type u} {B : Type v} [Ring R] [Ring B]
  {U : Type w} {V : Type t} [AddCommGroup U] [AddCommGroup V] [Module R U] [Module B V]

/-- Extending a defining submodule and changing compatible ambient coordinates commute. -/
theorem span_image_comap_equiv {φ : R →+* B} (f : U →ₛₗ[φ] V)
    (e : U ≃ₗ[R] U) (d : V ≃ₗ[B] V) (h : ∀ x, f (e x) = d (f x)) (N : Submodule R U) :
    Submodule.span B (f '' (N.comap e.toLinearMap : Set U)) =
      (Submodule.span B (f '' (N : Set U))).comap d.toLinearMap := by
  apply Submodule.map_injective_of_injective d.injective
  rw [Submodule.map_comap_eq_of_surjective d.surjective, Submodule.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨e x, hx, h x⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨f (e.symm x), ⟨e.symm x, ?_, rfl⟩, ?_⟩
    · change e (e.symm x) ∈ N
      simpa using hx
    · exact (h (e.symm x)).symm.trans (congrArg f (e.apply_symm_apply x))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chart.SubmoduleBaseChange
