import Mathlib.Algebra.Module.Projective

/-! # Quotient Retraction -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.QuotientRetraction

noncomputable section

/-! A submodule with projective quotient admits an actual linear retraction. -/

universe u v

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

theorem exists_projective_quotient_retraction (p : Submodule R M) [Module.Projective R (M ⧸ p)] :
    ∃ r : M →ₗ[R] p, r.comp p.subtype = LinearMap.id := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p.mkQ LinearMap.id p.mkQ_surjective
  let r : M →ₗ[R] p := (LinearMap.id - s.comp p.mkQ).codRestrict p (by
    intro x
    apply (Submodule.Quotient.mk_eq_zero p).mp
    change p.mkQ (x - s (p.mkQ x)) = 0
    rw [map_sub, ← LinearMap.comp_apply, hs, LinearMap.id_apply, sub_self])
  refine ⟨r, ?_⟩
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change x.val - s (p.mkQ x.val) = x.val
  have hx : p.mkQ x.val = 0 := (Submodule.Quotient.mk_eq_zero p).mpr x.property
  rw [hx, map_zero, sub_zero]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.QuotientRetraction
