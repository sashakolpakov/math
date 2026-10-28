import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.MonomialAlgebra

/-! # Monomial Finite Sums -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonomialFiniteSums

noncomputable section

/-! Finite exponent sums encode products of actual generators, and
their block degrees add exactly. -/
open scoped BigOperators Classical
universe u v w
variable {κ : Type u} [Fintype κ] {ι : Type v} {τ : Type w}

theorem monomialMultiDegree_single (w : κ → ι → ℕ) (k : κ) (i : ι) :
    Balanced.ExponentFiniteGeneration.monomialMultiDegree w (Pi.single k 1) i = w k i := by
  simp [Balanced.ExponentFiniteGeneration.monomialMultiDegree, Pi.single_apply]

theorem monomialMultiDegree_sum (w : κ → ι → ℕ) (s : Finset τ) (a : τ → κ → ℕ) (i : ι) :
    Balanced.ExponentFiniteGeneration.monomialMultiDegree w (∑ j ∈ s, a j) i = ∑ j ∈ s, Balanced.ExponentFiniteGeneration.monomialMultiDegree w (a j) i := by
  induction s using Finset.induction_on with
  | empty => simp [Balanced.ExponentFiniteGeneration.monomialMultiDegree]
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj, Balanced.ExponentFiniteGeneration.monomialMultiDegree_add, ih, Finset.sum_insert hj]

theorem exponentMonomial_single {A : Type v} [CommRing A] (D : κ → A) (k : κ) :
    Balanced.MonomialAlgebra.exponentMonomial D (Pi.single k 1) = D k := by
  simp [Balanced.MonomialAlgebra.exponentMonomial, Pi.single_apply]

theorem exponentMonomial_sum {A : Type v} [CommRing A]
    (D : κ → A) (s : Finset τ) (a : τ → κ → ℕ) :
    Balanced.MonomialAlgebra.exponentMonomial D (∑ j ∈ s, a j) = ∏ j ∈ s, Balanced.MonomialAlgebra.exponentMonomial D (a j) := by
  induction s using Finset.induction_on with
  | empty => simp [Balanced.MonomialAlgebra.exponentMonomial_zero]
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj, Balanced.MonomialAlgebra.exponentMonomial_add, ih, Finset.prod_insert hj]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonomialFiniteSums
