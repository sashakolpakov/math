import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Surjective Functional Kernel Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SurjectiveFunctionalKernelComparison

noncomputable section

/-! Two surjective scalar-valued linear functionals with the same
kernel differ by multiplication by a unit. The scalar is obtained by
evaluating any vector with value one under the first functional. -/
universe u v
variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]

theorem linearFunctional_factor_of_kernel_le (f g : V →ₗ[R] R)
    (hker : f.ker ≤ g.ker) (p : V) (hp : f p = 1) (x : V) :
    g x = f x * g p := by
  have hf : f (x - f x • p) = 0 := by
    rw [map_sub, map_smul, hp]
    simp only [smul_eq_mul, mul_one, sub_self]
  have hg : g (x - f x • p) = 0 := hker hf
  rw [map_sub, map_smul] at hg
  exact sub_eq_zero.mp hg

theorem linearFunctional_unitMultiple_of_equal_kernels
    (f g : V →ₗ[R] R) (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hker : f.ker = g.ker) : ∃ a : Rˣ, ∀ x, g x = (a : R) * f x := by
  obtain ⟨p, hp⟩ := hf 1
  obtain ⟨q, hq⟩ := hg 1
  have hprod : f q * g p = 1 :=
    (linearFunctional_factor_of_kernel_le f g hker.le p hp q).symm.trans hq
  let a : Rˣ := ⟨g p, f q, (mul_comm _ _).trans hprod, hprod⟩
  refine ⟨a, fun x => ?_⟩
  exact (linearFunctional_factor_of_kernel_le f g hker.le p hp x).trans (mul_comm _ _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SurjectiveFunctionalKernelComparison
