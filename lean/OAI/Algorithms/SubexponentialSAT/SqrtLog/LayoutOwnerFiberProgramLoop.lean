import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgramVisit

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def stream (ps : List (ℕ × ℕ)) : List Bool :=
  Encoding.encodeList (fun p => pairPayload p.1 p.2) ps

def fiberIndices (query : ℕ) : ℕ → List (ℕ × ℕ) → List ℕ
  | _, [] => []
  | index, p::ps => if p.1=query then index::fiberIndices query (index+1) ps
      else fiberIndices query (index+1) ps

def encodeIndices (is : List ℕ) : List Bool := is.flatMap Encoding.encodeNat

def scanCost (query : ℕ) : ℕ → List (ℕ × ℕ) → ℕ
  | _, [] => 1
  | index, p::ps => 6*(pairPayload p.1 p.2).length+callbackCost query index p+6+
      scanCost query (index+1) ps

def body : Code := .seq outerRead (.seq callback popScan)
def loop : Code := .while 0 body
def scan : Code := .seq popScan loop

theorem stream_head (ps : List (ℕ × ℕ)) : stream ps=(!ps.isEmpty)::(stream ps).tail := by
  cases ps <;> rfl

/-- Every plan record is physically read. The index advances even when the
owner comparison fails, so returned numbers are original incidence positions. -/
theorem loop_eval (ps : List (ℕ × ℕ)) (query index count : ℕ)
    (regs : Fin 5 → Bool) (master acc out : List Bool) :
    ∃ n ≤ scanCost query index ps, ∃ rf,
      Eval loop n
        (data (status regs (!ps.isEmpty) true) (unary query) master (stream ps).tail
          [] [] [] [] (unary index) acc (unary count) out)
        (data rf (unary query) master [] [] [] [] [] (unary (index+ps.length))
          ((encodeIndices (fiberIndices query index ps)).reverse++acc)
          (unary (count+(fiberIndices query index ps).length)) out) := by
  induction ps generalizing index count regs acc with
  | nil =>
      refine ⟨1,by simp [scanCost],status regs false true,?_⟩
      simpa [loop,stream,Encoding.encodeList,fiberIndices,encodeIndices] using
        (Eval.while_false (test := (0 : Fin 5)) (body := body)
          (a := data (status regs false true) (unary query) master [] [] [] [] []
            (unary index) acc (unary count) out) (by simp [data,status]))
  | cons p ps ih =>
      rcases p with ⟨v,f⟩
      have h1 := outerRead_eval (status regs true true) (unary query) master
        (pairPayload v f) (stream ps) (unary index) acc (unary count) out
      simp only [status_status] at h1
      obtain ⟨n2,hn2,r2,h2⟩ := callback_eval (status regs false true) query index count
        v f master (stream ps) acc out
      let acc' := if v=query then (Encoding.encodeNat index).reverse++acc else acc
      let count' := count+(if v=query then 1 else 0)
      have h3 := popScan_eval (reset r2) (!ps.isEmpty) (unary query) master
        (stream ps).tail (unary (index+1)) acc' (unary count') out
      rw [← stream_head ps] at h3
      obtain ⟨nt,hnt,rf,ht⟩ := ih (index+1) count' (reset r2) acc'
      have hb := h1.seq (h2.seq h3)
      have hh := Eval.while_true (test := (0 : Fin 5)) (by simp [data,status]) hb ht
      refine ⟨(6*(pairPayload v f).length+4)+(n2+1)+nt+1,?_,rf,?_⟩
      · simp only [scanCost]
        omega
      · convert hh using 1 <;>
          by_cases hv : v=query <;>
          simp [loop,body,stream,Encoding.encodeList,fiberIndices,encodeIndices,hv,
            acc',count',List.reverse_append,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem scan_eval (ps : List (ℕ × ℕ)) (query index count : ℕ)
    (regs : Fin 5 → Bool) (master acc out : List Bool) :
    ∃ n ≤ scanCost query index ps+1, ∃ rf,
      Eval scan n
        (data regs (unary query) master (stream ps) [] [] [] []
          (unary index) acc (unary count) out)
        (data rf (unary query) master [] [] [] [] [] (unary (index+ps.length))
          ((encodeIndices (fiberIndices query index ps)).reverse++acc)
          (unary (count+(fiberIndices query index ps).length)) out) := by
  have hp := popScan_eval regs (!ps.isEmpty) (unary query) master (stream ps).tail
    (unary index) acc (unary count) out
  rw [← stream_head ps] at hp
  obtain ⟨n,hn,rf,he⟩ := loop_eval ps query index count regs master acc out
  exact ⟨1+n,by omega,rf,hp.seq he⟩

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
