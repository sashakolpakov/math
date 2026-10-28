import Mathlib.LinearAlgebra.Determinant

/-! # Injective Determinant -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.InjectiveDeterminant

noncomputable section

/-! Injectivity of a map between free modules of the same finite rank
is equivalent to nonvanishing of its matrix determinant over a domain. -/

open _root_.Module
open scoped Classical

variable (R : Type*) [CommRing R] [IsDomain R]
  {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
  {ι : Type*} [Fintype ι]

theorem matrix_ne_zero (a : Basis ι R M) (b : Basis ι R N)
    (f : M →ₗ[R] N) (hf : Function.Injective f) :
    (LinearMap.toMatrix a b f).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hv₀⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have he := LinearMap.toMatrix_mulVec_repr a b f (a.equivFun.symm v)
  rw [← Basis.equivFun_apply, a.equivFun.apply_symm_apply, hv₀] at he
  have hz : f (a.equivFun.symm v) = 0 := by
    apply b.equivFun.injective
    exact he.symm.trans (map_zero b.equivFun).symm
  have h₀ : a.equivFun.symm v = 0 := hf (hz.trans (map_zero f).symm)
  apply hv
  simpa only [LinearEquiv.apply_symm_apply, map_zero] using congrArg a.equivFun h₀

theorem injective_of_matrix_ne_zero (a : Basis ι R M) (b : Basis ι R N)
    (f : M →ₗ[R] N) (hf : (LinearMap.toMatrix a b f).det ≠ 0) :
    Function.Injective f := by
  intro x y hxy
  by_contra hne
  apply hf
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨a.equivFun (x - y), a.equivFun.map_ne_zero_iff.mpr (sub_ne_zero.mpr hne), ?_⟩
  rw [Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr, map_sub, hxy, sub_self, map_zero]
  rfl

theorem end_ne_zero (b : Basis ι R M) (f : M →ₗ[R] M)
    (hf : Function.Injective f) : f.det ≠ 0 := by
  rw [← LinearMap.det_toMatrix b]
  exact matrix_ne_zero R b b f hf

theorem injective_of_end_ne_zero (b : Basis ι R M) (f : M →ₗ[R] M)
    (hf : f.det ≠ 0) : Function.Injective f := by
  apply injective_of_matrix_ne_zero R b b f
  rwa [LinearMap.det_toMatrix]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.InjectiveDeterminant
