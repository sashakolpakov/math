import OAI.NumberTheory.ArithmeticGroups.Lattices.DifferentialHullNormal
import OAI.NumberTheory.ArithmeticGroups.Lattices.DifferentialHullSolvable
import OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.DifferentialHull
import OAI.NumberTheory.ArithmeticGroups.Lattices.ExponentialNormal
import OAI.NumberTheory.ArithmeticGroups.Lattices.RationalGeometricEquiv

/-! # Algebraic Lie Radical -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.AlgebraicLieRadical.Construction

noncomputable section

/-! An algebraic proof that semisimplicity of an algebraic group kills
conjugation-stable solvable Lie algebras over every algebraically closed
field of characteristic zero. -/

open scoped Classical

attribute [local instance] LieRing.ofAssociativeRing

theorem algebraic_solvable_Lie_eq_bot_of_finite_normal_solvable
    {k : Type} [Field k] [CharZero k] [IsAlgClosed k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n)
    (hfinite : ∀ N : Subgroup G.RationalPoints, N.Normal → Group.IsSolvable N → Finite N)
    (S : LieSubalgebra k (Matrix (Fin n) (Fin n) k)) (hS : S ≤ Infinitesimal.Action.Construction.infinitesimalStabilizer G)
    [LieAlgebra.IsSolvable S]
    (hconj : ∀ g : G.RationalPoints, ∀ A ∈ S,
      (g.val : Matrix (Fin n) (Fin n) k) * A *
        ((g.val⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k) ∈ S) : S = ⊥ := by
  let : Finite (DifferentialHullGroup.Construction.differentialHullSubgroup G S) :=
    hfinite _ (DifferentialHullNormal.Construction.differentialHull_normal G S hconj) (DifferentialHullSolvable.Construction.differentialHull_solvable G S)
  apply le_antisymm _ bot_le
  intro A hA
  exact Lattices.Finite.DifferentialHull.Construction.finite_differentialHull_direction_zero G S hS hA

theorem algebraic_semisimple_solvable_Lie_eq_bot
    {k : Type} [Field k] [CharZero k] [IsAlgClosed k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsSemisimple)
    (S : LieSubalgebra k (Matrix (Fin n) (Fin n) k)) (hS : S ≤ Infinitesimal.Action.Construction.infinitesimalStabilizer G)
    [LieAlgebra.IsSolvable S]
    (hconj : ∀ g : G.RationalPoints, ∀ A ∈ S,
      (g.val : Matrix (Fin n) (Fin n) k) * A *
        ((g.val⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k) ∈ S) : S = ⊥ := by
  apply algebraic_solvable_Lie_eq_bot_of_finite_normal_solvable G _ S hS hconj
  intro N hN hsol
  let : N.Normal := hN
  let : Group.IsSolvable N := hsol
  exact RationalGeometricEquiv.Construction.semisimple_algClosed_normal_solvable_finite G hG N

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.AlgebraicLieRadical.Construction
