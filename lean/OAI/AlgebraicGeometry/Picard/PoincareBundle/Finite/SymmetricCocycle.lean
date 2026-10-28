import OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.CocycleCoalgebra
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.CoalgebraGroupLike
import OAI.AlgebraicGeometry.Picard.PoincareBundle.TwistedGroupLikeUnit

/-! # Symmetric Cocycle -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.SymmetricCocycle

noncomputable section

/-! Splitting symmetric unit cocycles over a finite commutative group scheme. -/

universe u v

open Coalgebra TensorProduct OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.CocycleCoalgebra

section

variable (k : Type u) (R : Type v) [Field k] [IsAlgClosed k] [CommRing R]
  [Bialgebra k R] [Coalgebra.IsCocomm k R] [Module.Finite k R] [Nontrivial R]
  (c : R ⊗[k] R) (hc : Symmetric.CocycleCoalgebra.IsNormalizedSymmetricCocycle k R c)

include hc

/-- Finite-dimensional duality produces a normalized solution of the twisted group-like equation. -/
theorem exists_solution :
    ∃ a : R, counit (R := k) a = 1 ∧ c * comul a = a ⊗ₜ[k] a := by
  have hcomm := Symmetric.CocycleCoalgebra.cocomm k R c hc
  let : Coalgebra k R := Symmetric.CocycleCoalgebra.coalgebra k R c hc
  let : Coalgebra.IsCocomm k R := hcomm
  obtain ⟨a, ha⟩ := CoalgebraGroupLike.exists_groupLike k R
  exact ⟨a, ha.counit_eq_one, ha.comul_eq_tmul_self⟩

end

variable (k : Type u) (R : Type v) [Field k] [IsAlgClosed k] [CommRing R]
  [HopfAlgebra k R] [Coalgebra.IsCocomm k R] [Module.Finite k R] [Nontrivial R]
  (c : (R ⊗[k] R)ˣ) (hc : Symmetric.CocycleCoalgebra.IsNormalizedSymmetricCocycle k R (c : R ⊗[k] R))

include hc

/-- Every normalized symmetric unit cocycle is a coboundary, including in positive characteristic. -/
theorem exists_unit_solution :
    ∃ a : Rˣ, counit (R := k) (a : R) = 1 ∧
      (c : R ⊗[k] R) * comul (a : R) = (a : R) ⊗ₜ[k] (a : R) := by
  obtain ⟨a, hε, hΔ⟩ := exists_solution k R (c : R ⊗[k] R) hc
  obtain ⟨u, rfl⟩ := TwistedGroupLikeUnit.isUnit_of_twisted_groupLike k R c a hε hΔ
  exact ⟨u, hε, hΔ⟩

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.SymmetricCocycle
