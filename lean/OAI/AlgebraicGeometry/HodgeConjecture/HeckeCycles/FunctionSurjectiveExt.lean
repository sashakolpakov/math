import Mathlib

/-! # Function Surjective Ext -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FunctionSurjectiveExt.CM

/-! Equality through two surjective changes of variables. -/

theorem of_two {A B C D : Type*} (v : B → C) (w : A → B)
    (hv : Function.Surjective v) (hw : Function.Surjective w) (f g : C → D)
    (h : ∀ a, f (v (w a)) = g (v (w a))) : f = g := by
  funext c
  obtain ⟨b, rfl⟩ := hv c
  obtain ⟨a, rfl⟩ := hw b
  exact h a

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FunctionSurjectiveExt.CM
