import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExactLength
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.FiniteType

/-! # Free Tensor Length -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FreeTensorLength

noncomputable section

/-! Tensoring by a finite free module multiplies length by its rank. -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable (R : Type u) [CommRing R] [Nontrivial R]

theorem tensor_length (M P : ModuleCat.{u} R) [Module.Free R P] [Module.Finite R P] :
    Module.length R (M ⊗[R] P) = (Module.finrank R P : ℕ∞) * Module.length R M := by
  rw [(TensorProduct.equivFinsuppOfBasisRight (Module.Free.chooseBasis R P)).length_eq,
    Module.length_finsupp]
  congr 1
  simpa [ENat.card] using congrArg (fun n : ℕ => (n : ℕ∞))
    (Module.finrank_eq_card_basis (Module.Free.chooseBasis R P)).symm

theorem tensor_length_ne_top (M P : ModuleCat.{u} R) [Module.Free R P] [Module.Finite R P]
    (hM : Module.length R M ≠ ⊤) : Module.length R (M ⊗[R] P) ≠ ⊤ := by
  rw [tensor_length R M P]
  lift Module.length R M to ℕ using hM with l hl
  rw [← Nat.cast_mul]
  exact ENat.natCast_ne_top _

theorem tensor_rationalLength (M P : ModuleCat.{u} R) [Module.Free R P] [Module.Finite R P] :
    ExactLength.rationalLength R (.of R (M ⊗[R] P)) =
      (Module.finrank R P : ℚ) * ExactLength.rationalLength R M := by
  unfold ExactLength.rationalLength
  rw [tensor_length R M P, ENat.toNat_mul, ENat.toNat_natCast, Nat.cast_mul]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FreeTensorLength
