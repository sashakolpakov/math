import Mathlib.Algebra.Module.Equiv.Basic

/-! # Linear Equiv Trans -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.LinearEquivTrans.LinearEquivComposition

noncomputable section

/-! A composition together with its evaluation rule, for keeping large comparison constructions opaque. -/

variable {R : Type*} [Semiring R] {M N P : Type*}
  [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
  [Module R M] [Module R N] [Module R P]

theorem exists_trans (e : M ≃ₗ[R] N) (f : N ≃ₗ[R] P) :
    ∃ g : M ≃ₗ[R] P, ∀ x, g x = f (e x) :=
  ⟨e.trans f, fun x => LinearEquiv.trans_apply (e₁₂ := e) (e₂₃ := f) x⟩

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.LinearEquivTrans.LinearEquivComposition
