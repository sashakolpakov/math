import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookupBasic
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup

abbrev unary (n : ℕ) : List Bool := List.replicate n true

def payload (p : ℕ × ℕ) : List Bool := pairKey (unary p.1) (unary p.2)
def records (ps : List (ℕ × ℕ)) : List (List Bool) := ps.map payload

theorem payload_injective : Function.Injective payload := by
  intro a b h
  have hf := Subexp.PackingMetadata.frame_injective h
  change Encoding.encodeList id [unary a.1,unary a.2] =
    Encoding.encodeList id [unary b.1,unary b.2] at hf
  have hp := Encoding.encodeList_injective Function.injective_id hf
  have hh : unary a.1=unary b.1 ∧ unary a.2=unary b.2 := by simpa using hp
  apply Prod.ext
  · simpa using congrArg List.length hh.1
  · simpa using congrArg List.length hh.2

theorem payload_original (v f : ℕ) :
    payload (v,f)=Subexp.PackingVertexLabels.planPayload [v,f] := rfl

theorem records_stream (ps : List (ℕ × ℕ)) :
    ProgramEncoding.encodeRecords (records ps)=LayoutOwnerFiberProgram.stream ps := by
  rw [LayoutOwnerFiberProgram.stream_original]
  rfl

theorem records_idxOf (ps : List (ℕ × ℕ)) (v f : ℕ) :
    (records ps).idxOf (pairKey (unary v) (unary f))=ps.idxOf (v,f) := by
  simpa only [List.idxOf,beq_eq_decide,records,payload] using
    Subexp.SeedIndexFormulas.idxOf_map_injective payload payload_injective ps (v,f)

end SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup

end OAI.Algorithms
