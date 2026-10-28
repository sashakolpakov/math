import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Exact.Basic

/-! # Exact Finrank -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ExactFinrank

/-! Dimension additivity for an actual short exact sequence of vector spaces. -/

universe u v w t

variable {K : Type u} [Field K]
variable {M : Type v} [AddCommGroup M] [Module K M]
variable {N : Type w} [AddCommGroup N] [Module K N] [Module.Finite K N]
variable {P : Type t} [AddCommGroup P] [Module K P]

theorem finrank_add_of_short_exact (i : M →ₗ[K] N) (p : N →ₗ[K] P)
    (hi : Function.Injective i) (hp : Function.Surjective p) (hex : Function.Exact i p) :
    Module.finrank K M + Module.finrank K P = Module.finrank K N := by
  have hker : Module.finrank K p.ker = Module.finrank K M :=
    ((LinearEquiv.ofInjective i hi).trans (LinearEquiv.ofEq _ _ hex.linearMap_ker_eq.symm)).finrank_eq.symm
  have hrange : Module.finrank K p.range = Module.finrank K P := by
    rw [LinearMap.range_eq_top.mpr hp, finrank_top]
  have h := p.finrank_range_add_finrank_ker
  rw [hker, hrange, Nat.add_comm] at h
  exact h

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ExactFinrank
