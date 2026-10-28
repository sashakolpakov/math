import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairs
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SupportProgramCount

/-! The active-coordinate pair iterator is paid by the supplied ambient
support envelope. These are cardinality comparisons, not stored families. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open BooleanDifferences

theorem supportFamily_card_eq_count (n J : ℕ) :
    (supportFamily n J).card = SqrtLog.SupportProgram.count n J := by
  rw [SqrtLog.SupportProgram.count_eq_supportUniverse]
  congr 1

theorem pairCount_le_ambient_support_square {m n : ℕ} (hmn : m ≤ n) (J : ℕ) :
    DifferencePairs.pairCount m J ≤ SqrtLog.SupportProgram.count n J ^ 2 := by
  have hcount : SqrtLog.SupportProgram.count m J ≤
      SqrtLog.SupportProgram.count n J := by
    unfold SqrtLog.SupportProgram.count
    exact Finset.sum_le_sum (fun j _ => Nat.choose_le_choose j hmn)
  calc
    DifferencePairs.pairCount m J ≤ (supportFamily m J).card ^ 2 :=
      DifferencePairs.pairCount_le_square m J
    _ = SqrtLog.SupportProgram.count m J ^ 2 := by rw [supportFamily_card_eq_count]
    _ ≤ SqrtLog.SupportProgram.count n J ^ 2 := Nat.pow_le_pow_left hcount 2

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
