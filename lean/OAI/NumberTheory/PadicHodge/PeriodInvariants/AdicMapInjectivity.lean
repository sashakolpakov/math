import Mathlib.RingTheory.AdicCompletion.Functoriality

/-! # Adic Map Injectivity -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicMapInjectivity

/-! # A map reflecting every adic filtration is injective on the actual completion -/

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] (I : Ideal R) (f : M →ₗ[R] N)
  (hf : ∀ n x, f x ∈ (I ^ n • ⊤ : Submodule R N) → x ∈ (I ^ n • ⊤ : Submodule R M))

include hf in
theorem quotient_injective (n : ℕ) : Function.Injective (f.reduceModIdeal (I ^ n)) := by
  have hz : ∀ x, f.reduceModIdeal (I ^ n) x = 0 → x = 0 := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      intro hx
      rw [LinearMap.reduceModIdeal_apply, Submodule.Quotient.mk_eq_zero] at hx
      rw [Submodule.Quotient.mk_eq_zero]
      exact hf n x hx
  intro x y h
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub, h, sub_self]

include hf in
theorem completion_injective : Function.Injective (AdicCompletion.map I f) := by
  intro x y h
  apply AdicCompletion.ext
  intro n
  apply quotient_injective I f hf n
  exact congrArg (fun z : AdicCompletion I N => z.val n) h

end OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicMapInjectivity
