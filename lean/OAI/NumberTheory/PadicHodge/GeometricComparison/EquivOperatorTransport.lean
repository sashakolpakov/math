import Mathlib

/-! # Equiv Operator Transport -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.EquivOperatorTransport

/-! Operator compatibility passes to the inverse of an actual equivalence. -/

theorem inverse_intertwines {X Y : Type*} (e : X ≃ Y) (f : X → X) (g : Y → Y)
    (h : ∀ x, e (f x) = g (e x)) (y : Y) : e.symm (g y) = f (e.symm y) := by
  apply e.injective
  exact (e.apply_symm_apply (g y)).trans
    ((congrArg g (e.apply_symm_apply y)).symm.trans (h (e.symm y)).symm)

end OAI.NumberTheory.PadicHodge.GeometricComparison.EquivOperatorTransport
