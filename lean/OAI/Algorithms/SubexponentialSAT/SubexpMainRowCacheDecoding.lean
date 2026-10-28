import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainRowCache
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowScalarDecode

namespace OAI.Algorithms

/-! The raw row decoder applied to the actual emitted source-cache bytes.
The node indices retain the concrete selected-quartic generator order. -/

namespace SubexponentialSAT.SubexpMainRowCache.CacheFacts

open SubexpMainProgram
open SubexpLayoutPorts (Allocation)

variable {er es p : ℕ} [Fact p.Prime] {alloc : Allocation es}
  {a : MainState er es} (h : CacheFacts alloc a p)

theorem inverse_decode (i : Fin (p^4 - 1)) :
    SubexpRawRow.scalarDecode h.source (h.inverse i) =
      ((SubexpMachineNodeOrder.nodeEquiv p i).val)⁻¹ := by
  rw [h.inverseEncoded i, flat_eq_encode,
    Subexp.UniversalRowScalarDecode.scalarDecode_encode]
  exact h.inverseValue i

theorem negative_decode (i : Fin (p^4 - 1)) :
    SubexpRawRow.scalarDecode h.source (h.negative i) =
      -(SubexpMachineNodeOrder.nodeEquiv p i).val := by
  rw [h.negativeEncoded i, flat_eq_encode,
    Subexp.UniversalRowScalarDecode.scalarDecode_encode]
  exact h.negativeValue i

/-- This includes diagonal entries, whose inverse difference is zero. -/
theorem difference_decode (i j : Fin (p^4 - 1)) :
    SubexpRawRow.scalarDecode h.source (h.difference i j) =
      ((SubexpMachineNodeOrder.nodeEquiv p i).val -
        (SubexpMachineNodeOrder.nodeEquiv p j).val)⁻¹ := by
  rw [h.differenceEncoded i j, flat_eq_encode,
    Subexp.UniversalRowScalarDecode.scalarDecode_encode]
  exact h.differenceValue i j

end SubexponentialSAT.SubexpMainRowCache.CacheFacts

end OAI.Algorithms
