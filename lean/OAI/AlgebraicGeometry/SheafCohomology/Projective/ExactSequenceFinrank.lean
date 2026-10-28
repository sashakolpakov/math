import OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteHomologySequence
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Exact Sequence Finrank -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.ExactSequenceFinrank

/-! Rank identities for exact pairs of finite-dimensional vector spaces. -/

open _root_.CategoryTheory
universe u v

theorem finrank_eq_ranges_of_exact
    {K : Type u} [Field K] {M N P : Type*}
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    [AddCommGroup P] [Module K P] [Module.Finite K N]
    (f : M →ₗ[K] N) (g : N →ₗ[K] P) (h : Function.Exact f g) :
    (Module.finrank K N : ℤ) =
      (Module.finrank K (LinearMap.range f) : ℤ) +
      (Module.finrank K (LinearMap.range g) : ℤ) := by
  have he := LinearMap.exact_iff.mp h
  have hd := g.finrank_range_add_finrank_ker
  rw [he] at hd
  omega

theorem shortComplex_finrank_eq_ranges
    {K : Type u} [Field K] (S : ShortComplex (ModuleCat.{v} K))
    [Module.Finite K S.X₂] (h : S.Exact) :
    (Module.finrank K S.X₂ : ℤ) =
      (Module.finrank K (LinearMap.range S.f.hom) : ℤ) +
      (Module.finrank K (LinearMap.range S.g.hom) : ℤ) :=
  finrank_eq_ranges_of_exact S.f.hom S.g.hom
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp h)

end OAI.AlgebraicGeometry.SheafCohomology.Projective.ExactSequenceFinrank
