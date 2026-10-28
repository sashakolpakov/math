import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgramWords
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTripleBridge

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open SubexponentialSAT.SubexpQuarticRing

theorem tableTape_eq_encoding {B d : ℕ} (table : Fin d → Fin d → Fin d → Word B) :
    tableTape table = RingTriple.tableEncoding table := by
  simp [tableTape, tableWords, RingTriple.tableEncoding, List.map_flatten, List.flatten_flatten,
    List.map_ofFn, Function.comp_def]

/-- The dense cached H-adic table occupies a fixed polynomial number of bits. -/
theorem ternary_tableTape_length (t : ℕ)
    (table : Fin (3*t) → Fin (3*t) → Fin (3*t) →
      SubexponentialSAT.SubexpQuarticRing.Word (SubexponentialSAT.SubexpLiftRing.baseWidth 3 t)) :
    (tableTape table).length = 54*t^4 := by
  rw [tableTape_length, RingProgram.ternary_baseWidth]
  ring


end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
