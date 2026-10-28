import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.QuotientInjective
import Mathlib.RingTheory.WittVector.DiscreteValuationRing

/-! # Quotient Injective -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.QuotientInjective

noncomputable section

/-! The actual finite Witt coefficient rings are injective over themselves,
so coefficient dualization is exact at each Witt level. -/

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]

theorem injective (n : ℕ) :
    Module.Injective (WittVector p k ⧸ (Ideal.span {(p : WittVector p k)}) ^ (n + 1))
      (WittVector p k ⧸ (Ideal.span {(p : WittVector p k)}) ^ (n + 1)) := by
  rw [Ideal.span_singleton_pow]
  exact Principal.QuotientInjective.injective ((p : WittVector p k) ^ (n + 1))
    (pow_ne_zero (n + 1) (WittVector.p_nonzero p k))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.QuotientInjective
