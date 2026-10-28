import OAI.RepresentationTheory.Theta.Geometric.SquareZero.Subalgebra
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-! # Factorization -/

namespace OAI.RepresentationTheory.Theta.Geometric.SquareZero.Factorization

noncomputable section

/-! A morphism constant modulo a square-zero subspace factors through the
actual split square-zero subalgebra, without requiring an augmentation of
the ambient algebra. -/

variable {M R A : Type*} [AddCommGroup M] [Module ℂ M] [Module ℂᵐᵒᵖ M]
    [IsCentralScalar ℂ M] [CommRing R] [Algebra ℂ R] [Nontrivial R]
    [CommRing A] [Algebra ℂ A]

omit [Nontrivial R] in
theorem squareZeroSubalgebraMap_mem_range
    (i : M →ₗ[ℂ] R) (hsq : ∀ x y, i x * i y = 0)
    (r : R) (c : ℂ) (h : r - algebraMap ℂ R c ∈ LinearMap.range i) :
    r ∈ (SquareZero.Subalgebra.squareZeroSubalgebraMap i hsq).range := by
  obtain ⟨m, hm⟩ := h
  refine ⟨TrivSqZeroExt.inl c + TrivSqZeroExt.inr m, ?_⟩
  change algebraMap ℂ R (c + 0) + i (0 + m) = r
  rw [add_zero, zero_add, hm, add_sub_cancel]

def squareZeroFactorization (i : M →ₗ[ℂ] R) (hi : Function.Injective i)
    (hsq : ∀ x y, i x * i y = 0) (f : A →ₐ[ℂ] R) (e : A →ₐ[ℂ] ℂ)
    (hf : ∀ a, f a - algebraMap ℂ R (e a) ∈ LinearMap.range i) :
    A →ₐ[ℂ] TrivSqZeroExt ℂ M :=
  (AlgEquiv.ofInjective (SquareZero.Subalgebra.squareZeroSubalgebraMap i hsq)
    (SquareZero.Subalgebra.squareZeroSubalgebraMap_injective i hi hsq)).symm.toAlgHom.comp
      (f.codRestrict _ (fun a => squareZeroSubalgebraMap_mem_range i hsq (f a) (e a) (hf a)))

theorem squareZeroFactorization_comp (i : M →ₗ[ℂ] R) (hi : Function.Injective i)
    (hsq : ∀ x y, i x * i y = 0) (f : A →ₐ[ℂ] R) (e : A →ₐ[ℂ] ℂ)
    (hf : ∀ a, f a - algebraMap ℂ R (e a) ∈ LinearMap.range i) :
    (SquareZero.Subalgebra.squareZeroSubalgebraMap i hsq).comp (squareZeroFactorization i hi hsq f e hf) = f := by
  ext a
  let eqv := AlgEquiv.ofInjective (SquareZero.Subalgebra.squareZeroSubalgebraMap i hsq)
    (SquareZero.Subalgebra.squareZeroSubalgebraMap_injective i hi hsq)
  have h := congrArg Subtype.val (eqv.apply_symm_apply
    (f.codRestrict _ (fun a => squareZeroSubalgebraMap_mem_range i hsq (f a) (e a) (hf a)) a))
  exact h

end

end OAI.RepresentationTheory.Theta.Geometric.SquareZero.Factorization
