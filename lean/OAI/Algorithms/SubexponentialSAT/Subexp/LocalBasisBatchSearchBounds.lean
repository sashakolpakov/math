import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchSearch
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchStorageBounds

namespace OAI.Algorithms

/-! Storage overhead around the actual local search, including old-bank cleanup. -/

namespace SubexponentialSAT.Subexp.LocalBasisBatchProgram

theorem searchInputs_disjoint :
    ∀ p ∈ searchInputs, ∀ q ∈ searchInputs, p.1 ≠ q.2 := by
  intro p hp q hq
  simp only [searchInputs, List.mem_cons, List.not_mem_nil, or_false] at hp hq
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem searchInputs_target (pair : Fin 128 × Fin 128) (hp : pair ∈ searchInputs) :
    65 ≤ pair.2.val ∧ pair.2.val < 107 := by
  simp only [searchInputs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem searchCopied_low (a : Data) (j : Fin 128) (hj : j.val < 65) :
    (searchCopied a).stacks j = a.stacks j := by
  apply copyMany_frame
  intro pair hp he
  have ht := searchInputs_target pair hp
  have hv := congrArg Fin.val he
  omega

theorem searchCost_le (p : ℕ) [Fact p.Prime] (alphabet : List (ZMod p))
    (m N : ℕ) (a : Data) (B : ℕ)
    (hsource : ∀ pair ∈ searchInputs, (a.stacks pair.1).length ≤ B)
    (hlow : ∀ j : Fin 128, j.val < 65 → (a.stacks j).length ≤ B) :
    searchCost p alphabet m N a ≤ 186 * B + 235 +
      BlockSearchExecution.cost (BlockSearchPredicate.scalarCode p) alphabet N
        (BlockCoefficientProgram.coefficientCost p m N) := by
  have hcopy := copyManyCost_le searchInputs a B searchInputs_disjoint hsource
  have hc : ∀ j ∈ matrixWork, ((searchCopied a).stacks j).length ≤ B := by
    intro j hj
    have hlt := (matrixWork_mem j).mp hj
    rw [searchCopied_low a j hlt]
    exact hlow j hlt
  have hclear := clearManyCost_le matrixWork (searchCopied a) B hc
  have hlen : searchInputs.length = 8 := rfl
  have hmatrix : matrixWork.length = 65 := by simp [matrixWork]
  rw [hlen] at hcopy
  rw [hmatrix] at hclear
  unfold searchCost
  omega

end SubexponentialSAT.Subexp.LocalBasisBatchProgram

end OAI.Algorithms
