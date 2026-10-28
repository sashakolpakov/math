import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramZero

namespace OAI.Algorithms

/-! Convert the Cartesian table to the exact nested moments schema. Every
representative is assembled from bucket representatives by native merge calls. -/
namespace SubexponentialSAT.SqrtLog.BucketTupleProgram.Representative

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport
open SubexponentialSAT.SqrtLog.MomentsAssembly (HeadInput BucketInput rawFrames)

abbrev Tuples := List (List HeadInput)

def bucket (n : ℕ) (heads : List HeadInput) : BucketInput :=
  ⟨representative heads (List.replicate n false),heads⟩

def tupleStep : Code :=
  .seq (readWord 0 1 14 (by decide))
  (.seq (copy 1 15 14)
  (.seq (copy 19 7 14)
  (.seq headCommand
  (.seq (emitFrame 15 2 14 (by decide))
  (.seq (emitFrame 7 2 14 (by decide))
        (emitFrame 2 8 14 (by decide)))))))

def tupleCost (heads : List HeadInput) (n : ℕ) : ℕ :=
  24*(headsBits heads).length + 15*n + 8*(2*n+2*(headsBits heads).length+2) +
  headsCost heads n + 42

theorem tupleStep_eval (regs : Fin 8 → Bool) (width tail out : List Bool) (heads : List HeadInput)
    (hv : ∀ h∈heads,Valid width.length h) :
    ∃ rf, Eval tupleStep (tupleCost heads width.length)
      (state regs width (Encoding.frame (headsBits heads)++tail) [] [] [] out)
      (state rf width tail [] [] [] (Encoding.frame (bucket width.length heads).bits++out)) := by
  let d := state regs width (Encoding.frame (headsBits heads)++tail) [] [] [] out
  obtain ⟨a,ha,hsa⟩ := readWord_eval (0 : Fin 20) 1 14
    (by decide) (by decide) (by decide) d (headsBits heads) tail rfl rfl rfl
  obtain ⟨b,hb,hsb⟩ := copy_eval (1 : Fin 20) 15 14
    (by decide) (by decide) (by decide) a (by simp [hsa,d,state])
  obtain ⟨c,hc,hsc⟩ := copy_eval (19 : Fin 20) 7 14
    (by decide) (by decide) (by decide) b (by simp [hsb,hsa,d,state,StackRoutines.copyStacks])
  have hec : c = state c.regs width tail (headsBits heads) (headsBits heads)
      (List.replicate width.length false) out := by
    apply congrArg (StructuredProgram.State.mk c.regs)
    funext i; fin_cases i <;> simp [hsc,hsb,hsa,d,state,StackRoutines.copyStacks]
  obtain ⟨rd,hd⟩ := headCommand_eval c.regs width tail (headsBits heads)
    (List.replicate width.length false) out heads width.length hv (by simp)
  rw [←hec] at hd
  let e := state rd width tail [] (headsBits heads)
    (representative heads (List.replicate width.length false)) out
  obtain ⟨f,hf,hsf⟩ := emitFrame_eval (15 : Fin 20) 2 14
    (by decide) (by decide) (by decide) e rfl
  obtain ⟨g,hg,hsg⟩ := emitFrame_eval (7 : Fin 20) 2 14
    (by decide) (by decide) (by decide) f (by simp [hsf,e,state])
  obtain ⟨h,hh,hsh⟩ := emitFrame_eval (2 : Fin 20) 8 14
    (by decide) (by decide) (by decide) g (by simp [hsg,hsf,e,state])
  have hend : h=state h.regs width tail [] [] []
      (Encoding.frame (bucket width.length heads).bits++out) := by
    apply congrArg (StructuredProgram.State.mk h.regs)
    funext i; fin_cases i <;>
      simp [hsh,hsg,hsf,e,state,bucket,BucketInput.bits,headsBits]
  have hr : (representative heads (List.replicate width.length false)).length=width.length :=
    representative_length heads _ width.length hv (by simp)
  have hall := ha.seq (hb.seq (hc.seq (hd.seq (hf.seq (hg.seq hh)))))
  change Eval tupleStep _ d h at hall
  rw [hend] at hall
  refine ⟨h.regs,?_⟩
  convert hall using 1
  simp [tupleCost,hsb,hsa,d,state,StackRoutines.copyStacks,hsg,hsf,e,hr,
    Encoding.length_frame]
  ; omega

def tupleReadTag : Code := .base (.atom (.pop 0 6 7))
def tupleReady (regs : Fin 8 → Bool) (width source out : List Bool) : Data :=
  state (readRegs regs 6 7 source.head?) width source.tail [] [] [] out

def tupleLoop : Code := .while 6 (.seq tupleStep tupleReadTag)
def tupleScan : Code := .seq tupleReadTag tupleLoop

def tuplesBits (tuples : Tuples) : List Bool := Encoding.encodeList headsBits tuples

def output (n : ℕ) (tuples : Tuples) (out : List Bool) : List Bool :=
  tuples.foldl (fun acc heads => Encoding.frame (bucket n heads).bits++acc) out

def scanCost (tuples : Tuples) (n : ℕ) : ℕ :=
  (tuples.map (fun heads => tupleCost heads n+2)).sum+2

theorem tupleReadTag_eval (regs : Fin 8 → Bool) (width source out : List Bool) :
    Eval tupleReadTag 1 (state regs width source [] [] [] out)
      (tupleReady regs width source out) := by
  have h := Eval.base (StructuredProgram.Eval.atom
    (.pop (0 : Fin 20) (6 : Fin 8) 7) (state regs width source [] [] [] out))
  unfold tupleReadTag
  convert h using 1
  apply congrArg (StructuredProgram.State.mk (readRegs regs 6 7 source.head?))
  funext i; fin_cases i <;> rfl

theorem tupleLoop_eval (regs : Fin 8 → Bool) (width out : List Bool) (tuples : Tuples)
    (hv : ∀ heads∈tuples,∀ h∈heads,Valid width.length h) :
    ∃ rf, Eval tupleLoop (scanCost tuples width.length-1)
      (tupleReady regs width (tuplesBits tuples) out)
      (state rf width [] [] [] [] (output width.length tuples out)) := by
  induction tuples generalizing regs out with
  | nil =>
      refine ⟨(tupleReady regs width (tuplesBits []) out).regs,?_⟩
      simpa [tupleLoop, scanCost,tuplesBits,Encoding.encodeList,tupleReady,state,output] using
        (Eval.while_false (show (tupleReady regs width (tuplesBits []) out).regs 6=false by
          simp [tupleReady,state,tuplesBits,Encoding.encodeList,readRegs]) : Eval tupleLoop 1 _ _)
  | cons heads tuples ih =>
      let rs := readRegs regs (6 : Fin 8) 7 (some true)
      obtain ⟨rm,hm⟩ := tupleStep_eval rs width (tuplesBits tuples) out heads
        (hv heads (by simp))
      obtain ⟨rf,hf⟩ := ih rm (Encoding.frame (bucket width.length heads).bits++out)
        (fun hs hh => hv hs (by simp [hh]))
      have hg : (tupleReady regs width (tuplesBits (heads::tuples)) out).regs 6=true := by
        simp [tupleReady,state,tuplesBits,Encoding.encodeList,readRegs]
      have hstart : tupleReady regs width (tuplesBits (heads::tuples)) out =
          state rs width (Encoding.frame (headsBits heads)++tuplesBits tuples) [] [] [] out := by
        simp [tupleReady,tuplesBits,Encoding.encodeList,rs]
      rw [←hstart] at hm
      have hall := Eval.while_true hg
        (hm.seq (tupleReadTag_eval rm width (tuplesBits tuples) _)) hf
      refine ⟨rf,?_⟩
      convert hall using 1
      · rfl
      · simp only [scanCost, List.map_cons, List.sum_cons]
        omega
      · apply congrArg (state rf width [] [] [] [])
        simp only [output, List.foldl_cons]

theorem tupleScan_eval (regs : Fin 8 → Bool) (width out : List Bool) (tuples : Tuples)
    (hv : ∀ heads∈tuples,∀ h∈heads,Valid width.length h) :
    ∃ rf, Eval tupleScan (scanCost tuples width.length)
      (state regs width (tuplesBits tuples) [] [] [] out)
      (state rf width [] [] [] [] (output width.length tuples out)) := by
  obtain ⟨rf,hf⟩ := tupleLoop_eval regs width out tuples hv
  have hall := (tupleReadTag_eval regs width (tuplesBits tuples) out).seq hf
  refine ⟨rf,?_⟩
  convert hall using 1
  · rfl
  · have hpos : 1 ≤ scanCost tuples width.length := by simp [scanCost]
    exact (Nat.add_sub_of_le hpos).symm

theorem output_eq (n : ℕ) (tuples : Tuples) (out : List Bool) :
    output n tuples out = rawFrames ((tuples.map (fun hs => (bucket n hs).bits)).reverse)++out := by
  induction tuples generalizing out with
  | nil => simp [output]
  | cons hs tuples ih =>
      change output n tuples (Encoding.frame (bucket n hs).bits++out)=_
      rw [ih]
      simp only [rawFrames_eq_words,List.map_cons,List.reverse_cons,words_append]
      simp [words,List.append_assoc]

def command : Code := .seq prepareZero tupleScan
def program := compiled command 0 8

def cost (width : List Bool) (tuples : Tuples) : ℕ :=
  11*width.length+8+scanCost tuples width.length

theorem command_eval (regs : Fin 8 → Bool) (width : List Bool) (tuples : Tuples)
    (hv : ∀ heads∈tuples,∀ h∈heads,Valid width.length h) :
    ∃ rf, Eval command (cost width tuples)
      (zeroStart regs width (tuplesBits tuples) [])
      (state rf width [] [] [] []
        (MomentsAssembly.bucketsInput ((tuples.map (bucket width.length)).reverse))) := by
  obtain ⟨ra,ha⟩ := prepareZero_eval regs width (tuplesBits tuples) []
  obtain ⟨rf,hf⟩ := tupleScan_eval ra width [] tuples hv
  have ho : output width.length tuples [] =
      MomentsAssembly.bucketsInput ((tuples.map (bucket width.length)).reverse) := by
    simp [output_eq,MomentsAssembly.bucketsInput,List.map_reverse,List.map_map,Function.comp_def]
  rw [ho] at hf
  exact ⟨rf,ha.seq hf⟩

theorem program_runsIn (regs : Fin 8 → Bool) (width : List Bool) (tuples : Tuples)
    (hv : ∀ heads∈tuples,∀ h∈heads,Valid width.length h) :
    ∃ rf, RunsIn program (cost width tuples+1)
      ((zeroStart regs width (tuplesBits tuples) []).withPC (some program.entry))
      ((state rf width [] [] [] []
        (MomentsAssembly.bucketsInput ((tuples.map (bucket width.length)).reverse))).withPC none) := by
  obtain ⟨rf,he⟩ := command_eval regs width tuples hv
  exact ⟨rf,cost width tuples+1,le_rfl,compiled_halt_trace he 0 8⟩

end SubexponentialSAT.SqrtLog.BucketTupleProgram.Representative

end OAI.Algorithms
