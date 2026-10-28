import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramSlots
import OAI.Algorithms.SubexponentialSAT.ProgramEncoding

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram

def rowRecords {m : ℕ} (b : ℕ) (rs : List (List (Fin m × SparseCode.F3))) : List Bool :=
  rs.flatMap fun row => true::Encoding.frame (rowPayload b m row)

def collectedRows {m : ℕ} (b : ℕ) (rs : List (List (Fin m × SparseCode.F3)))
    (tail : List Bool) : List Bool := rowRecords b rs.reverse++tail

@[simp] theorem collectedRows_nil {m : ℕ} (b : ℕ) (tail : List Bool) :
    collectedRows (m:=m) b [] tail=tail := rfl

theorem collectedRows_append {m : ℕ} (b : ℕ)
    (rs ss : List (List (Fin m × SparseCode.F3))) (tail : List Bool) :
    collectedRows b (rs++ss) tail=collectedRows b ss (collectedRows b rs tail) := by
  simp [collectedRows,rowRecords,List.reverse_append,List.flatMap_append,List.append_assoc]

theorem collectedRows_snoc {m : ℕ} (b : ℕ) (rs : List (List (Fin m × SparseCode.F3)))
    (row : List (Fin m × SparseCode.F3)) (tail : List Bool) :
    collectedRows b (rs++[row]) tail=
      true::(Encoding.frame (rowPayload b m row)++collectedRows b rs tail) := by
  simp [collectedRows,rowRecords,List.reverse_append,List.append_assoc]

theorem rowRecords_encodeList {m : ℕ} (b : ℕ)
    (rs : List (List (Fin m × SparseCode.F3))) :
    rowRecords b rs++[false]=Encoding.encodeList (rowPayload b m) rs := by
  induction rs with
  | nil => rfl
  | cons row rs ih =>
    simpa [rowRecords,Encoding.encodeList,List.append_assoc] using
      (congrArg (fun tail => true::(Encoding.frame (rowPayload b m row)++tail)) ih)

theorem collectedRows_encodeList {m : ℕ} (b : ℕ)
    (rs : List (List (Fin m × SparseCode.F3))) :
    collectedRows b rs [false]=Encoding.encodeList (rowPayload b m) rs.reverse :=
  rowRecords_encodeList b rs.reverse

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
