import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramIntegerEntry
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramLookupPair
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramStaging
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisEntryCore

namespace OAI.Algorithms

/-! The concrete incidence-entry program. Its read-only cache bank is200..211,
its input indices252/253, and the returned signed pair254/255. Ports212..251
belong to the caller and are outside every local subroutine map. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

abbrev Data := State 16 256
abbrev Code := Cmd 16 256

def lookupRegs : Fin 6 → Fin 16 := Fin.castAdd 10
def lookupPorts : Fin 16 → Fin 256 := ![200,252,253,64,65,66,67,68,69,70,71,72,73,74,75,76]
def integerRegs : Fin 10 → Fin 16 := Fin.castAdd 6
def integerPorts : Fin 64 → Fin 256 := Fin.castAdd 192

def blockPorts : Fin 32 → Fin 256 :=
  ![64,67,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29]
def indexPorts : Fin 32 → Fin 256 :=
  ![252,253,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29]

theorem lookupRegs_inj : Function.Injective lookupRegs := Fin.castAdd_injective _ _
theorem lookupPorts_inj : Function.Injective lookupPorts := by decide
theorem integerRegs_inj : Function.Injective integerRegs := Fin.castAdd_injective _ _
theorem integerPorts_inj : Function.Injective integerPorts := Fin.castAdd_injective _ _
theorem blockPorts_inj : Function.Injective blockPorts := by decide
theorem indexPorts_inj : Function.Injective indexPorts := by decide

def lookup : Code := .call (ProgramLinking.liftProgram LookupPair.program lookupRegs lookupPorts)
def compareBlocks : Code := liftCommand (GlobalBasisEntryCore.compare 0 1) 0 1 id blockPorts
def compareIndices : Code := liftCommand (GlobalBasisEntryCore.compare 0 1) 0 1 id indexPorts

def prepareOps : List (Staging.Action 256) :=
  [.copy 202 42,.copy 203 43,.copy 204 44,.copy 205 45,.copy 206 47,.copy 207 48,
   .copy 208 21,.copy 209 22,.copy 210 37,.copy 211 26,.copy 65 23,.copy 68 24,.push 25 true]
def prepare : Code := Staging.sequence 0 1 199 prepareOps

def integer : Code := liftCommand IntegerEntry.command 23 53 integerRegs integerPorts

def exportOps : List (Staging.Action 256) := [.copy 53 254,.copy 54 255]
def exportPair : Code := Staging.sequence 0 1 199 exportOps

def workPorts : List (Fin 256) := List.ofFn (fun i : Fin 200 => i.castAdd 56)
def cleanupOps : List (Staging.Action 256) := workPorts.map Staging.Action.clear
def cleanup : Code := Staging.sequence 0 1 199 cleanupOps

def covered : Code := .ite 5
  (.seq compareBlocks (.ite 7 (.seq prepare (.seq integer exportPair)) (.base .skip)))
  (.base .skip)
def uncovered : Code := .seq compareIndices
  (.ite 7 (TupleProgram.pushConst 254 0 true) (.base .skip))
def command : Code := .seq lookup (.seq (.ite 4 covered uncovered) cleanup)
def program := compiled command 252 254

theorem prepareOps_valid : ∀ op∈prepareOps,op.Valid (199:Fin 256) := by decide
theorem exportOps_valid : ∀ op∈exportOps,op.Valid (199:Fin 256) := by decide
theorem cleanupOps_valid : ∀ op∈cleanupOps,op.Valid (199:Fin 256) := by
  intro op hop
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hop
  trivial

theorem prepare_eval (a : Data) (ht : a.stacks 199=[]) :
    Eval prepare (Staging.cost 0 1 prepareOps a) a (Staging.result 0 1 prepareOps a) :=
  Staging.sequence_eval 0 1 199 (by decide) prepareOps a prepareOps_valid ht

theorem exportPair_eval (a : Data) (ht : a.stacks 199=[]) :
    Eval exportPair (Staging.cost 0 1 exportOps a) a (Staging.result 0 1 exportOps a) :=
  Staging.sequence_eval 0 1 199 (by decide) exportOps a exportOps_valid ht

theorem cleanup_eval (a : Data) (ht : a.stacks 199=[]) :
    Eval cleanup (Staging.cost 0 1 cleanupOps a) a (Staging.result 0 1 cleanupOps a) :=
  Staging.sequence_eval 0 1 199 (by decide) cleanupOps a cleanupOps_valid ht

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
