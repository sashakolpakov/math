import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BasisEvaluationMatrices
import Mathlib.Algebra.Module.Projective

/-! # Split Evaluation Cokernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SplitEvaluationCokernel

noncomputable section

/-! Evaluation with an actual left inverse has projective cokernel.
Precomposing it with a surjection does not change that cokernel. This
supplies the flatness required by scheme-theoretic matrix rank loci. -/
universe u v w z
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N] [Module.Projective R N]

theorem projective_cokernel_of_leftInverse (f : M →ₗ[R] N) (g : N →ₗ[R] M)
    (hgf : g.comp f = LinearMap.id) : Module.Projective R (N ⧸ f.range) := by
  let P : N →ₗ[R] N := LinearMap.id - f.comp g
  have hP : f.range ≤ P.ker := by
    rintro _ ⟨x, rfl⟩
    change f x - f (g (f x)) = 0
    rw [show g (f x) = x from LinearMap.congr_fun hgf x, sub_self]
  let s : (N ⧸ f.range) →ₗ[R] N := f.range.liftQ P hP
  have hs : f.range.mkQ.comp s = LinearMap.id := by
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := f.range.mkQ_surjective z
    change f.range.mkQ (x - f (g x)) = f.range.mkQ x
    rw [map_sub, show f.range.mkQ (f (g x)) = 0 from
      (Submodule.Quotient.mk_eq_zero f.range).mpr ⟨g x, rfl⟩, sub_zero]
  exact Module.Projective.of_split s f.range.mkQ hs

theorem projective_cokernel_of_split_surjective_factorization
    {V : Type z} [AddCommGroup V] [Module R V]
    (f : M →ₗ[R] N) (g : N →ₗ[R] M) (hgf : g.comp f = LinearMap.id)
    (q : V →ₗ[R] M) (hq : Function.Surjective q) :
    Module.Projective R (N ⧸ (f.comp q).range) := by
  have hr : (f.comp q).range = f.range := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨q x, rfl⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨z, rfl⟩ := hq x
      exact ⟨z, rfl⟩
  rw [hr]
  exact projective_cokernel_of_leftInverse f g hgf

theorem matrix_projective_cokernel_of_split_factorization
    {ι : Type v} {κ : Type w} {ν : Type z}
    [Fintype ι] [Fintype κ] [Fintype ν]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]
    (U : Matrix ι κ R) (B : Matrix κ ι R) (C : Matrix κ ν R)
    (hBU : B * U = 1) (hC : Function.Surjective (Matrix.toLin' C)) :
    Module.Projective R ((ι → R) ⧸ (Matrix.toLin' (U * C)).range) := by
  rw [Matrix.toLin'_mul]
  apply projective_cokernel_of_split_surjective_factorization (Matrix.toLin' U) (Matrix.toLin' B) _ _ hC
  rw [← Matrix.toLin'_mul, hBU, Matrix.toLin'_one]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SplitEvaluationCokernel
