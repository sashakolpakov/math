import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.PolynomialConstants

/-! # Infinitesimal Nonzero -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.InfinitesimalNonzero

noncomputable section

/-! A connected characteristic-zero matrix group with zero Lie algebra
has only the identity point over every field extension. -/

open scoped Classical
open OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.PolynomialConstants.Construction _root_.MvPolynomial

attribute [local instance] LieRing.ofAssociativeRing

variable {k : Type} [Field k] [CharZero k] {n : ℕ}

theorem point_eq_one_of_infinitesimal_eq_bot
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup k n) (hconn : G.IsGeometricallyConnected)
    (hL : ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G = ⊥)
    {K : Type} [Field K] (ι : k →+* K) (g : G.Points ι) : g = 1 := by
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have hp : ∀ A ∈ ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G,
      ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.rightInfinitesimal A (X (i, j)) ∈ ArithmeticGroups.Lattices.VanishingIdeal.Construction.coordinateVanishingIdeal G := by
    intro A hA
    rw [hL, LieSubalgebra.mem_bot] at hA
    rw [hA, ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.rightInfinitesimal_X]
    simp only [Matrix.zero_apply, map_zero, mul_zero, Finset.sum_const_zero]
    exact (ArithmeticGroups.Lattices.VanishingIdeal.Construction.coordinateVanishingIdeal G).zero_mem
  have he := ArithmeticGroups.Lattices.Infinitesimal.PolynomialConstants.Construction.evaluate_infinitesimal_invariant_constant G hconn (X (i, j)) hp ι g
  simpa [ArithmeticGroups.Lattices.Algebraic.evaluateMatrix, Matrix.one_apply] using he

theorem infinitesimal_nonzero_of_nontrivial_point
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup k n) (hconn : G.IsGeometricallyConnected)
    {K : Type} [Field K] (ι : k →+* K) (g : G.Points ι) (hg : g ≠ 1) :
    ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G ≠ ⊥ :=
  fun h => hg (point_eq_one_of_infinitesimal_eq_bot G hconn h ι g)

end

end OAI.NumberTheory.Quaternion.Arithmetic.InfinitesimalNonzero
