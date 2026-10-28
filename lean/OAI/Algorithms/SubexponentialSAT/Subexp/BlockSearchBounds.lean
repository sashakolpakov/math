import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchExecution
import OAI.Algorithms.SubexponentialSAT.Subexp.PairScoreBounds

namespace OAI.Algorithms

/-! A closed local bound including generation of all search data. -/

namespace SubexponentialSAT.Subexp.BlockSearchBounds

/-- This bound includes the actual tuple generation and the three nested
search loops. Its exponent depends on the local block dimension only. -/
theorem cost_le {K : Type*} (code : StackEncoding.BlockCode K) (alphabet : List K)
    (hA : 1 ≤ alphabet.length) (N bound : ℕ) :
    BlockSearchExecution.cost code alphabet N bound ≤
      800 * (N * N + 1) * alphabet.length ^ (N * N) * ((N * N + 1) * code.width + 1) +
      800 * (N + 1) * alphabet.length ^ N * ((N + 1) * code.width + 1) +
      6 * N ^ 2 + 22 * N + 37 +
      BlockSearchExecution.searchBound alphabet.length N code.width bound := by
  have ha : 1 ≤ (alphabet.map code.block).length := by simpa using hA
  have hw : ∀ row ∈ alphabet.map code.block, row.length ≤ code.width := by
    intro row hrow
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hrow
    exact (code.length_block x).le
  have ht := PairScoreBounds.generated_powerCost_le (alphabet.map code.block) (N * N)
    code.width ha hw
  have hc := PairScoreBounds.generated_powerCost_le (alphabet.map code.block) N code.width ha hw
  simp only [List.length_map] at ht hc
  unfold BlockSearchExecution.cost BlockSearchPreparation.cost
  simp only [List.length_replicate]
  omega

end SubexponentialSAT.Subexp.BlockSearchBounds

end OAI.Algorithms
