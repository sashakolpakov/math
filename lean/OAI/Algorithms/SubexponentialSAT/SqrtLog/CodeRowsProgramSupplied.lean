import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramRows
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCodeSupplied

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open scoped BigOperators
open SparseCode

theorem serializedRows_supplied_covers {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (s : SuppliedShifts m B) (Q : SuppliedLocal m B) (i : Fin (totalRows m B)) :
    suppliedMatrix m B hm hB s Q i ∈ (serializedRows m s Q).map coefficient := by
  exact serializedRows_covers s Q (graph_edge_lower hm hB) (rowEquiv m B i)

theorem serializedRows_kernel_bound {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (s : SuppliedShifts m B) (Q : SuppliedLocal m B)
    (hs : WalshExistence.Good (gapDenom m B) s)
    (hQ : HasDistance Q (degree m B / (100*B*logSize m)+1))
    (w : Fin m → F3)
    (hw : ∀ row ∈ serializedRows m s Q, (∑ c, coefficient row c*w c)=0)
    (hw0 : w≠0) : m ≤ distanceDenom m B*weight w := by
  apply supplied_kernel_bound_of_coverage hm hB s Q hs hQ
    ((serializedRows m s Q).map coefficient) (serializedRows_supplied_covers hm hB s Q) w _ hw0
  intro row hrow
  obtain ⟨slots,hslots,rfl⟩ := List.mem_map.mp hrow
  exact hw slots hslots

theorem serializedRows_supplied_length {m B : ℕ}
    (s : SuppliedShifts m B) (Q : SuppliedLocal m B) :
    (serializedRows m s Q).length=totalRows m B := by
  simpa [totalRows, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
    (serializedRows_length (m := m) s Q)

theorem serializedRows_supplied_slots {m B : ℕ}
    (s : SuppliedShifts m B) (Q : SuppliedLocal m B)
    (row : List (Fin m × F3)) (hrow : row∈serializedRows m s Q) :
    row.length ≤ degreeBound m B :=
  (serializedRows_slots_bound s Q row hrow).trans (degree_le_bound m B)

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
