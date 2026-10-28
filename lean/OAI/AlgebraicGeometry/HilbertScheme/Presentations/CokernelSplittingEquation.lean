import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.QuotientRetraction
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Cokernel Splitting Equation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.CokernelSplittingEquation

noncomputable section

/-! Flat cokernels of finite matrices are characterized by a finite matrix
equation. This supplies explicit splitting coefficients for descent. -/

universe u v w
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Projective R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

theorem cokernel_projective_iff_splitting_equation (f : N →ₗ[R] M) :
    Module.Projective R (M ⧸ f.range) ↔
      ∃ g : M →ₗ[R] N, f.comp (g.comp f) = f := by
  constructor
  · intro h
    let := h
    obtain ⟨r, hr⟩ := Presentations.Projective.QuotientRetraction.exists_projective_quotient_retraction f.range
    obtain ⟨g, hg⟩ := Module.projective_lifting_property f.rangeRestrict r f.surjective_rangeRestrict
    refine ⟨g, ?_⟩
    ext x
    have hx := LinearMap.congr_fun hg (f x)
    have hy := LinearMap.congr_fun hr (f.rangeRestrict x)
    exact (congrArg Subtype.val hx).trans (congrArg Subtype.val hy)
  · rintro ⟨g, hg⟩
    let s := LinearMap.id - f.comp g
    have hs : f.range ≤ s.ker := by
      rintro _ ⟨x, rfl⟩
      change f x - f (g (f x)) = 0
      exact sub_eq_zero.mpr (LinearMap.congr_fun hg x).symm
    let j := f.range.liftQ s hs
    apply Module.Projective.of_split j f.range.mkQ
    ext y
    change f.range.mkQ (y - f (g y)) = f.range.mkQ y
    rw [map_sub]
    have hz : f.range.mkQ (f (g y)) = 0 :=
      (Submodule.Quotient.mk_eq_zero f.range).mpr (LinearMap.mem_range_self f (g y))
    rw [hz, sub_zero]

variable {μ : Type v} {ν : Type w} [Fintype μ] [Fintype ν]
variable [DecidableEq μ] [DecidableEq ν]

theorem matrix_cokernel_flat_iff_splitting_equation (A : Matrix ν μ R) :
    Module.Flat R ((ν → R) ⧸ (Matrix.toLin' A).range) ↔
      ∃ X : Matrix μ ν R, A * X * A = A := by
  let f := Matrix.toLin' A
  let : Module.FinitePresentation R ((ν → R) ⧸ f.range) :=
    Module.finitePresentation_of_free_of_surjective f.range.mkQ f.range.mkQ_surjective (by
      rw [Submodule.ker_mkQ]
      exact Submodule.fg_range f)
  have hp : Module.Flat R ((ν → R) ⧸ f.range) ↔ Module.Projective R ((ν → R) ⧸ f.range) :=
    ⟨fun h => by let := h; exact Module.Flat.projective_of_finitePresentation, fun h => by let := h; infer_instance⟩
  rw [hp, cokernel_projective_iff_splitting_equation]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨LinearMap.toMatrix' g, ?_⟩
    apply Matrix.toLin'.injective
    simpa only [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', LinearMap.comp_assoc] using hg
  · rintro ⟨X, hX⟩
    refine ⟨Matrix.toLin' X, ?_⟩
    simpa only [Matrix.toLin'_mul, LinearMap.comp_assoc] using congrArg Matrix.toLin' hX

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.CokernelSplittingEquation
