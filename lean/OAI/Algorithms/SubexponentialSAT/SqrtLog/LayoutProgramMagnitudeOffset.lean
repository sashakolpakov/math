import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramMagnitude

namespace OAI.Algorithms

/-! The exact unsigned-pair budget accepted by the offset/signature pipeline. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram

theorem denominator_le_scalarBound (Q R : ℕ) (hQ : 1 ≤ Q) :
    2^(R-1) ≤ (8*Q)^(2*R) := by
  calc
    _ ≤ 2^(2*R) := Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ (8*Q)^(2*R) := Nat.pow_le_pow_left (by omega) _

theorem constraintMassBound_le (Q R : ℕ) (hQ : 1 ≤ Q) :
    constraintMassBound Q R ≤ 2*(8*Q)^(2*R) := by
  have h := denominator_le_scalarBound Q R hQ
  unfold constraintMassBound
  omega

/-- This proves the premise used by the physical subtraction W−N. It applies
to the actual separately stored components, with no canonical-sign premise. -/
theorem negative_le_offset {I : Type*} (fiber : List I)
    (positive negative : I → ℕ) (Q R B P N : ℕ) (hQ : 1 ≤ Q)
    (hB : fiber.length ≤ B)
    (h : ∀ i ∈ fiber, positive i + negative i ≤ constraintMassBound Q R)
    (hP : P = (fiber.map positive).sum) (hN : N = (fiber.map negative).sum) :
    P + N ≤ 2*B*(8*Q)^(2*R) ∧ N ≤ 2*B*(8*Q)^(2*R) := by
  have hb := pullback_components_le fiber positive negative Q R P N h hP hN
  have hmass := constraintMassBound_le Q R hQ
  have ht : fiber.length * constraintMassBound Q R ≤ 2*B*(8*Q)^(2*R) := by
    calc
      _ ≤ B * (2*(8*Q)^(2*R)) := Nat.mul_le_mul hB hmass
      _ = _ := by ring
  exact ⟨hb.1.trans ht, hb.2.trans ht⟩

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
