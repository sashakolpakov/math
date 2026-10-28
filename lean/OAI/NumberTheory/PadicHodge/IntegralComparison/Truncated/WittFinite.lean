import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt
import Mathlib.RingTheory.WittVector.Complete

/-! # Witt Finite -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.WittFinite

noncomputable section

/-!
# IntegralComparison: the actual bounded Witt coefficient ring is finite
-/

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]

theorem powerIdeal_eq_kernel (n : ℕ) :
    (Ideal.span {(p : WittVector p k)}) ^ (n + 1) =
      RingHom.ker (WittVector.truncate (p := p) (R := k) (n + 1)) := by
  ext x
  rw [Ideal.span_singleton_pow, WittVector.mem_span_p_pow_iff_le_coeff_eq_zero,
    WittVector.mem_ker_truncate]

def equivTruncated (n : ℕ) :
    Witt.Ring p k n ≃+* TruncatedWittVector p (n + 1) k :=
  (Ideal.quotEquivOfEq (powerIdeal_eq_kernel p k n)).trans
    (RingHom.quotientKerEquivOfSurjective (WittVector.truncate_surjective (p := p) (n := n + 1) (R := k)))

theorem finite [Finite k] (n : ℕ) : Finite (Witt.Ring p k n) := by
  let : Finite (TruncatedWittVector p (n + 1) k) := inferInstanceAs (Finite (Fin (n + 1) → k))
  exact Finite.of_injective _ (equivTruncated p k n).injective

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.WittFinite
