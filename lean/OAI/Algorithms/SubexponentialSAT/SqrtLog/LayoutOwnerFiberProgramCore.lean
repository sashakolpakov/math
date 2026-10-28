import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingVertexLabels
import OAI.Algorithms.SubexponentialSAT.SubexpNodeIndexProgram
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Native owner-fiber scan primitives. Original ambient IDs are compared as
unary strings; the emitted indices count positions in the actual plan stream. -/
namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 5 11
abbrev Code := Cmd 5 11
abbrev unary (n : ℕ) := List.replicate n true

def status (regs : Fin 5 → Bool) (v p : Bool) : Fin 5 → Bool :=
  Function.update (Function.update regs 0 v) 1 p

def data (regs : Fin 5 → Bool)
    (query master scan payload decoded work tmp index acc count out : List Bool) : Data :=
  ⟨regs,![query,master,scan,payload,decoded,work,tmp,index,acc,count,out]⟩

@[simp] theorem status_status (regs : Fin 5 → Bool) (v p v' p' : Bool) :
    status (status regs v p) v' p'=status regs v' p' := by
  funext i; fin_cases i <;> simp [status]

@[simp] theorem status_read (regs : Fin 5 → Bool) :
    readRegs regs (0 : Fin 5) 1 none=status regs false false := by
  funext i; fin_cases i <;> rfl

def forward : Code := .call (StackRoutines.transferProgram 3 4 0 1)

theorem forward_eval (regs : Fin 5 → Bool)
    (q m s bits w t i a c o : List Bool) :
    Eval forward (3*bits.length+3)
      (data regs q m s bits.reverse [] w t i a c o)
      (data (status regs false false) q m s [] bits w t i a c o) := by
  have h := transfer_eval (data regs q m s bits.reverse [] w t i a c o)
    3 4 0 1 (by decide) (by decide)
  convert h using 1
  · rfl
  · simp [data]
  · apply state_ext
    · simp [afterTransfer,data]
    · funext j; fin_cases j <;> simp [afterTransfer,data,StackRoutines.transferStacks]

def readPorts : RecordPrograms.Ports 5 11 where
  tag:=0; present:=1; found:=4; source:=4; payload:=3
  tag_ne_present:=by decide
  found_ne_tag:=by decide
  found_ne_present:=by decide
  source_ne_payload:=by decide

def readFrame : Code := RecordPrograms.reader readPorts

theorem read_state (regs : Fin 5 → Bool)
    (q m s payload decoded w t i a c o bits tail : List Bool) (v p : Bool) :
    RecordPrograms.state readPorts (data regs q m s payload decoded w t i a c o)
      v p (regs 4) tail bits = data (status regs v p) q m s bits tail w t i a c o := by
  apply state_ext
  · funext j; fin_cases j <;> simp [RecordPrograms.state,readPorts,data,status]
  · funext j; fin_cases j <;> simp [RecordPrograms.state,readPorts,data]

theorem readFrame_eval (regs : Fin 5 → Bool)
    (q m s bits tail w t i a c o : List Bool) :
    Eval readFrame (6*bits.length+4)
      (data regs q m s [] (Encoding.frame bits++tail) w t i a c o)
      (data (status regs false true) q m s bits.reverse tail w t i a c o) := by
  have h := RecordPrograms.reader_eval readPorts
    (data regs q m s [] (Encoding.frame bits++tail) w t i a c o)
    bits tail [] (regs 0) (regs 1) (regs 4)
  rw [read_state,read_state] at h
  have he : status regs (regs 0) (regs 1)=regs := by
    funext j; fin_cases j <;> simp [status]
  simpa [readFrame,he] using h

def popDecoded : Code := .base (.atom (.pop 4 0 1))

theorem popDecoded_eval (regs : Fin 5 → Bool) (b : Bool)
    (q m s payload tail w t i a c o : List Bool) :
    Eval popDecoded 1 (data regs q m s payload (b::tail) w t i a c o)
      (data (status regs b true) q m s payload tail w t i a c o) := by
  have h := Eval.base (StructuredProgram.Eval.atom (.pop (4 : Fin 11) (0 : Fin 5) 1)
    (data regs q m s payload (b::tail) w t i a c o))
  convert h using 1
  · rfl
  · apply state_ext
    · funext j; fin_cases j <;> simp [data,status,StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,
      execInstr,readRegs]
    · funext j; fin_cases j <;> simp [data,StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,execInstr]

def clear (src : Fin 11) : Code := .call (StackRoutines.clearProgram src 0 1)
def cleared (d : Data) (src : Fin 11) : Data :=
  ⟨status d.regs false false,Function.update d.stacks src []⟩

theorem clear_eval (src : Fin 11) (d : Data) :
    Eval (clear src) (2*(d.stacks src).length+3) d (cleared d src) := by
  have h := ListRegisterProgram.clear_run src (0 : Fin 5) 1 d.regs d.stacks
  apply Eval.call
  simpa [clear,cleared,StructuredProgram.State.withPC,StackRoutines.clearStacks] using h

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
