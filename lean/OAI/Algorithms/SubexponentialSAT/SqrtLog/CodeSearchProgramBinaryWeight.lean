import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramParity

namespace OAI.Algorithms

/-! The physical support counter recognizes the exceptional zero Walsh
character exactly. This is independent of any graph goodness assumption. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open scoped BigOperators

theorem binary_weight_zero_iff {r : ℕ} (a : Cayley.Cube r) :
    cellWeight ((List.ofFn a).map binaryCell) = 0 ↔ a = 0 := by
  rw [cellWeight_binary,List.map_ofFn,List.sum_ofFn]
  constructor
  · intro hz
    change (∑ j : Fin r, if a j ≠ 0 then (1 : ℕ) else 0) = 0 at hz
    funext i
    have hi : (if a i ≠ 0 then 1 else 0 : ℕ) ≤
        ∑ j : Fin r, if a j ≠ 0 then 1 else 0 :=
      Finset.single_le_sum (f := fun j : Fin r => if a j ≠ 0 then (1 : ℕ) else 0)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [hz] at hi
    change a i = 0
    by_contra h
    simp [h] at hi
  · rintro rfl
    simp

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
