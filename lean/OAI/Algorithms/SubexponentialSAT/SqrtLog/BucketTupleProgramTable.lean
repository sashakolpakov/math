import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
import OAI.Algorithms.SubexponentialSAT.WorkspaceCleanupProgram

namespace OAI.Algorithms

/-! Paid conversion of one attained-bucket table into a Cartesian alphabet.
The assignments remain a complete framed list inside each alphabet word. -/
namespace SubexponentialSAT.SqrtLog.BucketTupleProgram.Table

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

abbrev Data := State 8 8
abbrev Code := Cmd 8 8
abbrev Bucket := List Bool × List (List Bool)

def payload (b : Bucket) : List Bool := Encoding.frame b.1 ++ words b.2

def headBits (mask context : List Bool) (b : Bucket) : List Bool :=
  Encoding.frame mask ++ Encoding.frame context ++ Encoding.frame (words b.2)

def alphabetWord (mask context : List Bool) (b : Bucket) : List Bool :=
  Encoding.frame (headBits mask context b)

def state (regs : Fin 8 → Bool) (mask context source out : List Bool) : Data :=
  ⟨regs, ![source,[],[],[],mask,context,out,[]]⟩

def step : Code :=
  .seq (readWord 0 2 3 (by decide))
  (.seq (readFrame 2 1 (by decide))
  (.seq (WorkspaceCleanupProgram.command 0 1 [1])
  (.seq (emitFrame 2 1 3 (by decide))
  (.seq (copy 5 2 3)
  (.seq (emitFrame 2 1 3 (by decide))
  (.seq (copy 4 2 3)
  (.seq (emitFrame 2 1 3 (by decide))
  (.seq (emitFrame 1 2 3 (by decide))
  (.seq (emitFrame 2 6 3 (by decide))
        (SubexponentialSAT.Subexp.TupleProgram.pushConst 6 0 true))))))))))

def stepCost (mask context : List Bool) (b : Bucket) : ℕ :=
  9*(payload b).length + 8*b.1.length + 8*(words b.2).length +
  15*context.length + 15*mask.length + 24*(headBits mask context b).length + 74

theorem step_eval (regs : Fin 8 → Bool) (mask context tail out : List Bool) (b : Bucket) :
    ∃ rf, Eval step (stepCost mask context b)
      (state regs mask context (Encoding.frame (payload b)++tail) out)
      (state rf mask context tail
        (true :: (Encoding.frame (alphabetWord mask context b)++out))) := by
  let d := state regs mask context (Encoding.frame (payload b)++tail) out
  obtain ⟨a,ha,hsa⟩ := readWord_eval (0 : Fin 8) 2 3
    (by decide) (by decide) (by decide) d (payload b) tail rfl rfl rfl
  obtain ⟨c,hc,hsc⟩ := readFrame_eval (2 : Fin 8) 1 (by decide) a b.1 (words b.2)
    (by simp [hsa,payload]) (by simp [hsa,d,state])
  let e := WorkspaceCleanupProgram.finish (0 : Fin 8) 1 ([1] : List (Fin 8)) c
  have he := WorkspaceCleanupProgram.command_eval (0 : Fin 8) 1
    ([1] : List (Fin 8)) (by decide) c
  obtain ⟨f,hf,hsf⟩ := emitFrame_eval (2 : Fin 8) 1 3
    (by decide) (by decide) (by decide) e
    (by simp [e,hsc,hsa,d,state])
  obtain ⟨g,hg,hsg⟩ := copy_eval (5 : Fin 8) 2 3
    (by decide) (by decide) (by decide) f
    (by simp [hsf,e,hsc,hsa,d,state])
  obtain ⟨h,hh,hsh⟩ := emitFrame_eval (2 : Fin 8) 1 3
    (by decide) (by decide) (by decide) g
    (by simp [hsg,hsf,e,hsc,hsa,d,state,StackRoutines.copyStacks])
  obtain ⟨i,hi,hsi⟩ := copy_eval (4 : Fin 8) 2 3
    (by decide) (by decide) (by decide) h
    (by simp [hsh,hsg,hsf,e,hsc,hsa,d,state,StackRoutines.copyStacks])
  obtain ⟨j,hj,hsj⟩ := emitFrame_eval (2 : Fin 8) 1 3
    (by decide) (by decide) (by decide) i
    (by simp [hsi,hsh,hsg,hsf,e,hsc,hsa,d,state,StackRoutines.copyStacks])
  obtain ⟨k,hk,hsk⟩ := emitFrame_eval (1 : Fin 8) 2 3
    (by decide) (by decide) (by decide) j
    (by simp [hsj,hsi,hsh,hsg,hsf,e,hsc,hsa,d,state,StackRoutines.copyStacks])
  obtain ⟨l,hl,hsl⟩ := emitFrame_eval (2 : Fin 8) 6 3
    (by decide) (by decide) (by decide) k
    (by simp [hsk,hsj,hsi,hsh,hsg,hsf,e,hsc,hsa,d,state,StackRoutines.copyStacks])
  let m := SubexponentialSAT.Subexp.TupleProgram.pushedState (6 : Fin 8) 0 true l
  have hm := SubexponentialSAT.Subexp.TupleProgram.pushConst_eval (6 : Fin 8) 0 true l
  have hend : m = state m.regs mask context tail
      (true :: (Encoding.frame (alphabetWord mask context b)++out)) := by
    apply congrArg (StructuredProgram.State.mk m.regs)
    funext q; fin_cases q <;>
      simp [hsl,hsk,hsj,hsi,hsh,hsg,hsf,e,
        hsc,hsa,d,state,StackRoutines.copyStacks,
        alphabetWord,headBits,List.append_assoc]
  have hall := ha.seq (hc.seq (he.seq (hf.seq (hg.seq (hh.seq
    (hi.seq (hj.seq (hk.seq (hl.seq hm)))))))))
  change Eval step _ d m at hall
  rw [hend] at hall
  refine ⟨m.regs, ?_⟩
  convert hall using 1
  simp [stepCost,WorkspaceCleanupProgram.cost,hsk,hsj,hsi,hsh,hsg,hsf,e,hsc,hsa,d,state,
    StackRoutines.copyStacks,headBits,payload,Encoding.length_frame]
  ; omega

def readTag : Code := .base (.atom (.pop 0 6 7))
def tagged (regs : Fin 8 → Bool) (mask context source out : List Bool) : Data :=
  state (readRegs regs 6 7 source.head?) mask context source.tail out

theorem readTag_eval (regs : Fin 8 → Bool) (mask context source out : List Bool) :
    Eval readTag 1 (state regs mask context source out) (tagged regs mask context source out) := by
  have h := Eval.base (StructuredProgram.Eval.atom
    (.pop (0 : Fin 8) (6 : Fin 8) 7) (state regs mask context source out))
  change Eval readTag 1 (state regs mask context source out) _ at h
  convert h using 1
  apply congrArg (StructuredProgram.State.mk (readRegs regs 6 7 source.head?))
  funext i; fin_cases i <;> rfl

def loop : Code := .while 6 (.seq step readTag)
def command : Code := .seq readTag loop

def tableBits (bs : List Bucket) : List Bool := Encoding.encodeList payload bs

def output (mask context : List Bool) (bs : List Bucket) (out : List Bool) : List Bool :=
  bs.foldl (fun acc b => true :: (Encoding.frame (alphabetWord mask context b)++acc)) out

def cost (mask context : List Bool) (bs : List Bucket) : ℕ :=
  (bs.map (fun b => stepCost mask context b+2)).sum+2

theorem loop_eval (regs : Fin 8 → Bool) (mask context : List Bool) (bs : List Bucket)
    (out : List Bool) : ∃ rf, Eval loop (cost mask context bs-1)
      (tagged regs mask context (tableBits bs) out)
      (state rf mask context [] (output mask context bs out)) := by
  induction bs generalizing regs out with
  | nil =>
      refine ⟨(tagged regs mask context (tableBits []) out).regs, ?_⟩
      change Eval (.while 6 (.seq step readTag)) 1 _ _
      convert (Eval.while_false (show (tagged regs mask context (tableBits []) out).regs 6=false by
          simp [tagged,state,tableBits,Encoding.encodeList,readRegs]) :
          Eval (.while 6 (.seq step readTag)) 1 _ _) using 1 ;
        simp [tableBits,Encoding.encodeList,tagged,state,output]
  | cons b bs ih =>
      let rs := readRegs regs (6 : Fin 8) 7 (some true)
      obtain ⟨rm,hm⟩ := step_eval rs mask context (tableBits bs) out b
      obtain ⟨rf,hf⟩ := ih rm (true :: (Encoding.frame (alphabetWord mask context b)++out))
      have hg : (tagged regs mask context (tableBits (b::bs)) out).regs 6=true := by
        simp [tagged,state,tableBits,Encoding.encodeList,readRegs]
      have hstart : tagged regs mask context (tableBits (b::bs)) out =
          state rs mask context (Encoding.frame (payload b)++tableBits bs) out := by
        simp [tagged,tableBits,Encoding.encodeList,rs]
      rw [←hstart] at hm
      have hall := Eval.while_true hg (hm.seq (readTag_eval rm mask context (tableBits bs) _)) hf
      refine ⟨rf, ?_⟩
      change Eval (.while 6 (.seq step readTag)) _ _ _
      change Eval (.while 6 (.seq step readTag)) _ _ _ at hall
      convert hall using 1 <;> simp [cost,output,List.foldl_cons] ; omega

theorem command_eval (regs : Fin 8 → Bool) (mask context : List Bool) (bs : List Bucket)
    (out : List Bool) : ∃ rf, Eval command (cost mask context bs)
      (state regs mask context (tableBits bs) out)
      (state rf mask context [] (output mask context bs out)) := by
  obtain ⟨rf,hf⟩ := loop_eval regs mask context bs out
  refine ⟨rf, ?_⟩
  have hall := (readTag_eval regs mask context (tableBits bs) out).seq hf
  change Eval (.seq readTag loop) _ _ _
  change Eval (.seq readTag loop) _ _ _ at hall
  convert hall using 1 ; simp [cost] ; omega

theorem output_eq (mask context : List Bool) (bs : List Bucket) (acc : List (List Bool)) :
    output mask context bs (ProgramEncoding.encodeRecords acc) =
      ProgramEncoding.encodeRecords ((bs.map (alphabetWord mask context)).reverse++acc) := by
  induction bs generalizing acc with
  | nil => simp [output]
  | cons b bs ih =>
      change output mask context bs
        (ProgramEncoding.encodeRecords (alphabetWord mask context b::acc)) = _
      rw [ih]
      simp [List.reverse_cons,List.append_assoc]

def program := compiled command 0 6

theorem program_runsIn (regs : Fin 8 → Bool) (mask context : List Bool) (bs : List Bucket) :
    ∃ rf, RunsIn program (cost mask context bs+1)
      ((state regs mask context (tableBits bs) [false]).withPC (some program.entry))
      ((state rf mask context []
        (ProgramEncoding.encodeRecords (bs.map (alphabetWord mask context)).reverse)).withPC none) := by
  obtain ⟨rf,he⟩ := command_eval regs mask context bs [false]
  have ho := output_eq mask context bs []
  simp only [List.append_nil] at ho
  change output mask context bs [false] = _ at ho
  rw [ho] at he
  exact ⟨rf,cost mask context bs+1,le_rfl,compiled_halt_trace he 0 6⟩

end SubexponentialSAT.SqrtLog.BucketTupleProgram.Table

end OAI.Algorithms
