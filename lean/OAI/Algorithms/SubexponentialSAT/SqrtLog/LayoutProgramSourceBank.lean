import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSource
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramLiteral
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramTypeCompare
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramLookupPair
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramStaging
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgramDefinitions
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowMismatchTypes
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisEntryCore

namespace OAI.Algorithms

/-! Actual packed source dispatch. This program constructs each polynomial
source from computed metadata and raw scalar caches, not a supplied polynomial
table. The owner-fiber source sum is a separate outer traversal. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

abbrev Data := State 16 320
abbrev Code := Cmd 16 320

def lookupRegs : Fin 6 → Fin 16 := Fin.castAdd 10
def lookupPorts : Fin 16 → Fin 320 := ![306,304,305,288,289,290,291,292,293,294,295,296,297,298,299,300]
def lowRegs : Fin 10 → Fin 16 := Fin.castAdd 6
def lowPorts : Fin 64 → Fin 320 := Fin.castAdd 256
def vectorPorts : Fin 256 → Fin 320 := Fin.castAdd 64

def mismatchPorts : Fin 49 → Fin 320 :=
  fun j => if h : j.val < 42 then ⟨j.val,by omega⟩ else ⟨j.val+26,by omega⟩
def emitterRegs : Fin 8 → Fin 16 := Fin.castAdd 8
def emitterPorts : Fin 32 → Fin 320 := fun j=>⟨256+j.val,by omega⟩
def comparePorts (left right : Fin 320) : Fin 32 → Fin 320 :=
  ![left,right,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,301,15,16,17,18,19,20,21,22,23,303,302,24,25,307]

def lookup : Code := .call (ProgramLinking.liftProgram LookupPair.program lookupRegs lookupPorts)
def compareBlocks : Code := liftCommand (GlobalBasisEntryCore.compare 0 1) 0 1 id (comparePorts 288 291)
def compareIndices : Code := liftCommand (GlobalBasisEntryCore.compare 0 1) 0 1 id (comparePorts 304 305)
def compareTypes : Code := liftCommand TypeCompare.command 23 23 lowRegs lowPorts

def vector : Code := .call (ProgramLinking.liftProgram LayoutSourceValuesProgram.Native.tableProgram id vectorPorts)
def mismatches : Code := liftCommand UniversalRowMismatchTypes.command 23 45 lowRegs mismatchPorts

def stageTypesOps : List (Staging.Action 320) := [.copy 289 23,.copy 292 24]
def stageTypes : Code := Staging.sequence 0 1 319 stageTypesOps

def delta : Code := .ite 7
  (Staging.action 0 1 319 (.copy 314 274))
  (Staging.action 0 1 319 (.copy 313 274))

def stageEmitterOps : List (Staging.Action 320) :=
  [.copy 67 280,.copy 308 281,.copy 309 282,.copy 310 283,.copy 71 284,
   .copy 311 285,.copy 312 286,.copy 313 259,.copy 314 266,.copy 47 269]
def stageEmitter : Code := Staging.sequence 0 1 319 stageEmitterOps

def emit : Code := .call (ProgramLinking.liftProgram UniversalRowSourceProgram.program emitterRegs emitterPorts)
def universal : Code := .seq stageTypes (.seq vector (.seq mismatches (.seq compareTypes
  (.seq delta (.seq stageEmitter emit)))))

def literalRegs : Fin 3 → Fin 16 := Fin.castAdd 13
def literalPorts (src : Fin 320) : Fin 4 → Fin 320 := ![src,315,316,287]
def literal (src : Fin 320) : Code :=
  liftCommand Literal.command 0 3 literalRegs (literalPorts src)
def zero : Code := literal 313
def one : Code := literal 314

def covered : Code := .ite 5 (.seq compareBlocks (.ite 7 universal zero)) zero
def uncovered : Code := .seq compareIndices (.ite 7 one zero)

def cleanupPorts : List (Fin 320) :=
  [23,24,67,68,69,70,71,72,73,74] ++
  (List.ofFn fun j : Fin 31 => (⟨256+j.val,by omega⟩ : Fin 320)) ++
  (List.ofFn fun j : Fin 16 => (⟨288+j.val,by omega⟩ : Fin 320)) ++ [307,315,316]
def cleanupOps : List (Staging.Action 320) := cleanupPorts.map Staging.Action.clear
def cleanup : Code := Staging.sequence 0 1 319 cleanupOps

def command : Code := .seq lookup (.seq (.ite 4 covered uncovered) cleanup)
def program := compiled command 304 287

theorem stageTypes_valid : ∀ op∈stageTypesOps,op.Valid (319:Fin 320) := by decide
theorem stageEmitter_valid : ∀ op∈stageEmitterOps,op.Valid (319:Fin 320) := by decide
theorem stageTypes_eval (a : Data) (ht : a.stacks 319=[]) :
    Eval stageTypes (Staging.cost 0 1 stageTypesOps a) a (Staging.result 0 1 stageTypesOps a) :=
  Staging.sequence_eval 0 1 319 (by decide) stageTypesOps a stageTypes_valid ht

theorem stageEmitter_eval (a : Data) (ht : a.stacks 319=[]) :
    Eval stageEmitter (Staging.cost 0 1 stageEmitterOps a) a (Staging.result 0 1 stageEmitterOps a) :=
  Staging.sequence_eval 0 1 319 (by decide) stageEmitterOps a stageEmitter_valid ht

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
