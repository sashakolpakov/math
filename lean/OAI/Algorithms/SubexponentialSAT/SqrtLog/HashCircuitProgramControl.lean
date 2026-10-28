import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramFrame
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramRecords

namespace OAI.Algorithms

/-! Fixed record-control code for sparse-hash evaluation. This module fixes
all parsing and traversal code. Arithmetic components below are finite native
commands, to be instantiated by the separate dictionary modules; no semantic
function is called by the machine. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev copy (src dst tmp : Fin 96) : Cmd 8 96 :=
  .call (StackRoutines.copyProgram src dst tmp (0 : Fin 8) 1)
abbrev clear (src : Fin 96) : Cmd 8 96 :=
  .call (StackRoutines.clearProgram src (0 : Fin 8) 1)
abbrev transfer (src dst : Fin 96) : Cmd 8 96 :=
  .call (StackRoutines.transferProgram src dst (0 : Fin 8) 1)

def copied (d : Machine) (src dst : Fin 96) : Machine :=
  ⟨readRegs d.regs 0 1 none,StackRoutines.copyStacks src dst d.stacks⟩
def cleared (d : Machine) (src : Fin 96) : Machine :=
  ⟨readRegs d.regs 0 1 none,StackRoutines.clearStacks src d.stacks⟩
def transferred (d : Machine) (src dst : Fin 96) : Machine :=
  ⟨readRegs d.regs 0 1 none,StackRoutines.transferStacks src dst d.stacks⟩

theorem copy_eval (d : Machine) (src dst tmp : Fin 96)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (htmp : d.stacks tmp = []) :
    Eval (copy src dst tmp) (7*(d.stacks src).length+5) d (copied d src dst) := by
  apply Eval.call
  have h := StackRoutines.copyProgram_trace src dst tmp (0 : Fin 8) 1 hsd hst htd
    (by decide) d.regs d.stacks htmp
  have hh := StackRoutines.halt_after_trace _ h 7 rfl rfl
  simpa [copied,StackRoutines.copyResult,StructuredProgram.State.withPC,
    StackRoutines.copyProgram,Nat.add_assoc] using hh

theorem clear_eval (d : Machine) (src : Fin 96) :
    Eval (clear src) (2*(d.stacks src).length+3) d (cleared d src) := by
  apply Eval.call
  have h := StackRoutines.clearProgram_trace src (0 : Fin 8) 1 d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 2 rfl rfl
  simpa [cleared,StackRoutines.clearResult,StructuredProgram.State.withPC,
    StackRoutines.clearProgram,Nat.add_assoc] using hh

theorem transfer_eval (d : Machine) (src dst : Fin 96) (hsd : src ≠ dst) :
    Eval (transfer src dst) (3*(d.stacks src).length+3) d (transferred d src dst) := by
  apply Eval.call
  have h := StackRoutines.transferProgram_trace src dst (0 : Fin 8) 1 hsd (by decide) d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 3 rfl rfl
  simpa [transferred,StackRoutines.transferResult,StructuredProgram.State.withPC,
    StackRoutines.transferProgram,Nat.add_assoc] using hh

def literalPorts : RecordPrograms.Ports 8 96 :=
  ⟨0,1,2,63,58,by decide,by decide,by decide,by decide⟩
def rowPorts : RecordPrograms.Ports 8 96 :=
  ⟨0,1,2,64,66,by decide,by decide,by decide,by decide⟩

/-- Both record loops use this physical three-instruction return convention. -/
abbrev recordReturn : Cmd 8 96 :=
  .seq (.base (.atom (.set 0 false)))
    (.seq (.base (.atom (.set 1 true))) (.base (.atom (.set 2 false))))

def returned (d : Machine) : Machine :=
  { d with regs := Function.update (Function.update (Function.update d.regs 0 false) 1 true) 2 false }

theorem recordReturn_eval (d : Machine) : Eval recordReturn 3 d (returned d) := by
  exact (Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 8) false) d)).seq
    ((Eval.base (StructuredProgram.Eval.atom (.set (1 : Fin 8) true) _)).seq
      (Eval.base (StructuredProgram.Eval.atom (.set (2 : Fin 8) false) _)))

/-- Concrete fixed commands are supplied here, rather than semantic ring
operations. Their ABI is: complement61, product(67,61)→67 consuming61,
and scalar-weighted accumulation(65,67,68)→68 consuming65/67. -/
structure Arithmetic where
  oneMinus : Cmd 8 96
  multiply : Cmd 8 96
  scaleAdd : Cmd 8 96

/-- The polarity branch is taken before arithmetic may reuse the registers. -/
abbrev literalStep (arith : Arithmetic) : Cmd 8 96 :=
  .seq fetchLiteral
    (.seq (.ite 5 arith.oneMinus (.base .skip))
      (.seq arith.multiply recordReturn))

abbrev clauseLoop (arith : Arithmetic) : Cmd 8 96 :=
  RecordPrograms.iterate literalPorts (literalStep arith)

/-- Each clause starts from a physical preserving copy of the cached one. -/
abbrev weightedClauseStep (arith : Arithmetic) : Cmd 8 96 :=
  .seq openWeighted
    (.seq (copy 69 67 70)
      (.seq (clauseLoop arith) (.seq arith.scaleAdd recordReturn)))

/-- One fixed dynamic outer loop, independent of the number of clauses,
literals, hash entries, variable count and numeric precisions. -/
abbrev rowLoop (arith : Arithmetic) : Cmd 8 96 :=
  RecordPrograms.iterate rowPorts (weightedClauseStep arith)

abbrev rowCommand (arith : Arithmetic) : Cmd 8 96 :=
  .seq (clear 68) (rowLoop arith)

def rowProgram (arith : Arithmetic) := compiled (rowCommand arith) 64 68

@[simp] theorem returned_stack (d : Machine) (i : Fin 96) :
    (returned d).stacks i = d.stacks i := rfl

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

end OAI.Algorithms
