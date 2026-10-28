import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Encoding

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashScopeProgram

def recordPrefix : List (List Bool) → List Bool
  | [] => []
  | x :: xs => true :: (Encoding.frame x ++ recordPrefix xs)

theorem encodeRecords_eq (xs : List (List Bool)) :
    Encoding.encodeList id xs = recordPrefix xs ++ [false] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Encoding.encodeList, recordPrefix, ih, List.append_assoc]

theorem recordPrefix_append (xs ys : List (List Bool)) :
    recordPrefix (xs ++ ys) = recordPrefix xs ++ recordPrefix ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [recordPrefix, ih, List.append_assoc]

theorem prefix_encodeRecords (xs ys : List (List Bool)) :
    recordPrefix xs ++ Encoding.encodeList id ys = Encoding.encodeList id (xs ++ ys) := by
  simp [encodeRecords_eq, recordPrefix_append, List.append_assoc]

def clauseBytes (bits : List Bool) : List Bool :=
  ((Encoding.readFrame bits).map Prod.snd).getD []

@[simp] theorem clauseBytes_payload (weight : List Bool) (records : List (List Bool)) :
    clauseBytes (Encoding.frame weight ++ Encoding.encodeList id records) =
      Encoding.encodeList id records := by simp [clauseBytes]

def accumulate (bits out : List Bool) : List Bool := (clauseBytes bits).dropLast ++ out

@[simp] theorem accumulate_payload (weight : List Bool) (records : List (List Bool)) (out : List Bool) :
    accumulate (Encoding.frame weight ++ Encoding.encodeList id records) out =
      recordPrefix records ++ out := by
  unfold accumulate
  rw [clauseBytes_payload, encodeRecords_eq]
  simp

end SubexponentialSAT.SqrtLog.HashScopeProgram

end OAI.Algorithms
