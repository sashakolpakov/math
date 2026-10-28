import OAI.AlgebraicGeometry.Picard.PoincareBundle.AlgebraCocycleAssociativity

/-! # Algebra Cocycle Splitting -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.AlgebraCocycleSplitting

noncomputable section

/-! A natural symmetric regular cocycle on a finite commutative group has a regular splitting. -/

universe u

open Coalgebra TensorProduct OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalAlgebraCocycle OAI.AlgebraicGeometry.Picard.PoincareBundle.CocyclePointEvaluation

variable (k R : Type u) [Field k] [IsAlgClosed k] [CommRing R] [HopfAlgebra k R]
  [Coalgebra.IsCocomm k R] [Module.Finite k R] [Nontrivial R]
  (C : NaturalAlgebraCocycle.NaturalCocycle k R)

/-- The solution is one unit of the coordinate ring, uniformly valid on every test algebra. -/
theorem exists_unit_splitting :
    ∃ a : Rˣ, counit (R := k) (a : R) = 1 ∧
      ∀ (S : Type u) [CommRing S] [Algebra k S] (x y : R →ₐ[k] S),
        C.value x y * Units.map (CocyclePointEvaluation.product k R S x y).toMonoidHom a =
          Units.map x.toMonoidHom a * Units.map y.toMonoidHom a := by
  obtain ⟨a, hε, hΔ⟩ := PoincareBundle.Finite.SymmetricCocycle.exists_unit_solution k R (NaturalAlgebraCocycle.coordinate k R C)
    (AlgebraCocycleAssociativity.normalizedSymmetricCocycle k R C)
  refine ⟨a, hε, ?_⟩
  intro S _ _ x y
  rw [← NaturalAlgebraCocycle.evaluate_coordinate k R C]
  exact CocyclePointEvaluation.solution_at_points k R S (NaturalAlgebraCocycle.coordinate k R C) a hΔ x y

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.AlgebraCocycleSplitting
