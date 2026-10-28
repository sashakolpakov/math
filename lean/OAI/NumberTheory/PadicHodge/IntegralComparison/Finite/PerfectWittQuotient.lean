import Mathlib.RingTheory.WittVector.Complete

/-! # Perfect Witt Quotient -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PerfectWittQuotient

noncomputable section

/-! Every actual p-power Witt quotient of a finite perfect ring is finite. -/

variable (p : ℕ) [Fact p.Prime] (A : Type*) [CommRing A] [CharP A p] [PerfectRing A p]

theorem kernel (n : ℕ) : (Ideal.span {(p : WittVector p A)}) ^ (n + 1) =
    RingHom.ker (WittVector.truncate (p := p) (R := A) (n + 1)) := by
  ext x
  rw [Ideal.span_singleton_pow, WittVector.mem_span_p_pow_iff_le_coeff_eq_zero,
    WittVector.mem_ker_truncate]

def equiv (n : ℕ) : (WittVector p A ⧸ (Ideal.span {(p : WittVector p A)}) ^ (n + 1)) ≃+*
    TruncatedWittVector p (n + 1) A :=
  (Ideal.quotEquivOfEq (kernel p A n)).trans
    (RingHom.quotientKerEquivOfSurjective (WittVector.truncate_surjective (p := p) (n := n + 1) (R := A)))

theorem finite [Finite A] (n : ℕ) :
    Finite (WittVector p A ⧸ (Ideal.span {(p : WittVector p A)}) ^ (n + 1)) := by
  let : Finite (TruncatedWittVector p (n + 1) A) := inferInstanceAs (Finite (Fin (n + 1) → A))
  exact Finite.of_injective _ (equiv p A n).injective

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PerfectWittQuotient
