import Mathlib.LinearAlgebra.Pi

/-! # Constant Pi Coordinates -/

namespace OAI.RepresentationTheory.Theta.Geometric.ConstantPiCoordinates

/-! Reindexing a constant family of linear coordinates is literal
precomposition by the inverse index equivalence. -/

open Function

theorem linearPiCongrLeft_constant {K V α β : Type*} [Semiring K]
    [AddCommMonoid V] [Module K V] (e : α ≃ β) (f : α → V) :
    LinearEquiv.piCongrLeft K (fun _ : β => V) e f = f ∘ e.symm := by
  funext b
  change (Equiv.piCongrLeft' (fun _ : β => V) e.symm).symm f b = f (e.symm b)
  rw [Equiv.piCongrLeft'_symm]
  rfl

end OAI.RepresentationTheory.Theta.Geometric.ConstantPiCoordinates
