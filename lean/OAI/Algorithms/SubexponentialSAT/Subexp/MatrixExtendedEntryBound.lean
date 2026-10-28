import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryBudgetBounds

namespace OAI.Algorithms

/-! A common-size polynomial bound for the actual zero-extended entry
program. The underlying estimate includes its extractor, scan, padding,
Pascal additions, selection, sign and cleanup costs. -/

namespace SubexponentialSAT.Subexp.MatrixExtendedEntryBound

open MulticolorTypes MatrixWordEncoding

/-- A degree-four cap when every runtime size is at most a positive `S`. -/
def entryBound (S : ℕ) : ℕ := 6400000 * S ^ 4

theorem monotone_entryBound : Monotone entryBound := by
  intro S T h
  exact Nat.mul_le_mul_left 6400000 (Nat.pow_le_pow_left h 4)

variable {r Q Δ : ℕ}

/-- This bounds the concrete service budget, without an assumed execution
or callback-cost premise. A separate bound on the encoded type width is
unnecessary because it follows from the three type parameters. -/
theorem programBudget_le (p : ℕ) [Fact p.Prime] (i : Fin Δ) (t : Fin Q)
    (u y : UniversalType r Q Δ) (xs : List (ZMod p)) (S : ℕ)
    (hS : 1 ≤ S) (hr : r ≤ S) (hQ : Q ≤ S) (hΔ : Δ ≤ S)
    (hR : xs.length ≤ S) (hw : width p ≤ S) :
    MatrixExtendedEntryProgram.programBudget p i t u y xs ≤ entryBound S := by
  calc
    _ ≤ 400000 * (S + 1) ^ 4 :=
      MatrixEntryBudgetBounds.extended_programBudget_le p i t u y xs S hr hQ hΔ hR hw
    _ ≤ 400000 * (2 * S) ^ 4 :=
      Nat.mul_le_mul_left 400000 (Nat.pow_le_pow_left (by omega) 4)
    _ = entryBound S := by unfold entryBound; ring

end SubexponentialSAT.Subexp.MatrixExtendedEntryBound

end OAI.Algorithms
