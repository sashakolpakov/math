import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Algebra.Hom

/-! # Linear Multiplicativity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.LinearMultiplicativity

noncomputable section

/-! Multiplicativity of a linear map extends from spanning generators
by bilinearity, for possibly noncommutative target algebras. -/

theorem linearMap_mul_on_span {R A B I : Type*} [CommSemiring R]
    [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
    (v : I → A) (f : A →ₗ[R] B)
    (hf : ∀ i j, f (v i * v j) = f (v i) * f (v j))
    {x y : A} (hx : x ∈ Submodule.span R (Set.range v))
    (hy : y ∈ Submodule.span R (Set.range v)) : f (x * y) = f x * f y := by
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    exact hf i j
  | zero_left y hy => simp only [zero_mul, map_zero]
  | zero_right x hx => simp only [mul_zero, map_zero]
  | add_left x₁ x₂ y hx₁ hx₂ hy h₁ h₂ => simp only [add_mul, map_add, h₁, h₂]
  | add_right x y₁ y₂ hx hy₁ hy₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂]
  | smul_left r x y hx hy h => simp only [smul_mul_assoc, map_smul, h]
  | smul_right r x y hx hy h => simp only [mul_smul_comm, map_smul, h]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.LinearMultiplicativity
