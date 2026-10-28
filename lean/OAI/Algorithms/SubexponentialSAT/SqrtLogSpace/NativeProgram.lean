import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ABI
import OAI.Algorithms.SubexponentialSAT.CounterForPrograms
import OAI.Algorithms.SubexponentialSAT.Encoding
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.FrontendProgram
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

/-! Actual finite count-word positivity suffix. The counting body is integrated
separately; this suffix never interprets the least significant bit as SAT. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls

def positivity {r s : ℕ} (ports : CounterForPrograms.Ports r s)
    (answer : Fin s) : Cmd r s :=
  .seq (CounterForPrograms.testCmd ports)
    (.base (.atom (.push answer (ports.register 2))))

noncomputable def positivityResult {r s : ℕ} (ports : CounterForPrograms.Ports r s)
    (answer : Fin s) (a : State r s) : State r s :=
  (StructuredProgram.Atom.push answer (ports.register 2)).eval
    (CounterForPrograms.testResult ports a)

def positivityPorts : CounterForPrograms.Ports 80 1220 where
  register := ABI.positivityRegisters
  counter := ABI.countStack
  scratch := ABI.positivityScratch
  counter_ne_scratch := by decide

def clearOutput (port : Fin 1220) : Cmd 80 1220 :=
  .call (StackRoutines.clearProgram port 72 73)

def clearOutputState (port : Fin 1220) (a : State 80 1220) : State 80 1220 :=
  ⟨readRegs a.regs 72 73 none, Function.update a.stacks port []⟩

def answerReady (a : State 80 1220) : State 80 1220 :=
  clearOutputState ABI.positivityScratch (clearOutputState ABI.answerStack a)

noncomputable def answerResult (a : State 80 1220) : State 80 1220 :=
  positivityResult positivityPorts ABI.answerStack (answerReady a)

def answerCommand : Cmd 80 1220 :=
  .seq (clearOutput ABI.answerStack)
    (.seq (clearOutput ABI.positivityScratch) (positivity positivityPorts ABI.answerStack))

def answerProgram := compiled answerCommand ABI.countStack ABI.answerStack

def answerSteps (a : State 80 1220) : ℕ :=
  2 * (a.stacks ABI.answerStack).length + 2 * (a.stacks ABI.positivityScratch).length +
    8 * (a.stacks ABI.countStack).length + 15

/-- Each unary header bit contributes one zero; the initial one is retained. -/
def powerBody : Cmd 2 2 :=
  .base (.seq (.atom (.set 0 false))
    (.seq (.atom (.push 1 0)) (.atom (.pop 0 0 1))))

def powerSeed : Cmd 2 2 :=
  .base (.seq (.atom (.set 0 true))
    (.seq (.atom (.push 1 0)) (.atom (.pop 0 0 1))))

def powerCommand : Cmd 2 2 := .seq powerSeed (.while 0 powerBody)

def powerProgram := compiled powerCommand 0 1

def powerState (flag : Bool) (unread output : List Bool) : State 2 2 :=
  ⟨![flag, true], ![unread, output]⟩

def powerBoundary (n : ℕ) (output : List Bool) : State 2 2 :=
  match n with
  | 0 => powerState false [] output
  | n + 1 => powerState true (Encoding.encodeNat n) output

def headerStacks : Fin 4 ↪ Fin 1220 where
  toFun := ![1218, 268, 267, 269]
  inj' := by decide

def copyInput : Cmd 80 1220 :=
  .call (StackRoutines.copyProgram ABI.countStack 1218 1219 72 73)

def copiedInput (input : List Bool) : State 80 1220 :=
  ⟨fun _ => false, Function.update (StructuredProgram.ioState (r := 80) ABI.countStack input).stacks
    1218 input⟩

def headerCommand : Cmd 80 1220 := .seq copyInput
  (.call (ProgramLinking.liftProgram FrontendProgram.initializeProgram
    ABI.positivityRegisters headerStacks))

def headerProgram := compiled headerCommand ABI.countStack ABI.answerStack

noncomputable def headerResult (input body binary : List Bool) : State 80 1220 :=
  embedState ABI.positivityRegisters headerStacks (copiedInput input)
    (StructuredProgram.State.ofCfg (FrontendProgram.cfg none false false body [] binary []))

def copyWord (src dst scratch : Fin 1220) : Cmd 80 1220 :=
  .call (StackRoutines.copyProgram src dst scratch 72 73)

def copiedWord (src dst : Fin 1220) (a : State 80 1220) : State 80 1220 :=
  ⟨readRegs a.regs 72 73 none, StackRoutines.copyStacks src dst a.stacks⟩

/-- This list is fixed finite control, never an input-dependent work list. -/
def clearSequence : List (Fin 1220) → Cmd 80 1220
  | [] => .base .skip
  | port :: rest => .seq (clearOutput port) (clearSequence rest)

private opaque leafPortsWrapped :
    {ports : List (Fin 1220) // ports = (List.finRange 896).map ABI.leafStacks} :=
  ⟨(List.finRange 896).map ABI.leafStacks, rfl⟩

/-- The fixed leaf-bank ports, kept opaque so unrelated command proofs do not
reduce the complete 896-element cleanup table. -/
def leafPorts : List (Fin 1220) := leafPortsWrapped.1

theorem leafPorts_eq : leafPorts = (List.finRange 896).map ABI.leafStacks :=
  leafPortsWrapped.2

def clearLeaf : Cmd 80 1220 := clearSequence leafPorts

def resetRegisters : List (Fin 80) → Cmd 80 1220
  | [] => .base .skip
  | i :: rest => .seq (.base (.atom (.set i false))) (resetRegisters rest)

def resetRegisterState (ports : List (Fin 80)) (a : State 80 1220) : State 80 1220 :=
  ⟨fun i => if i ∈ ports then false else a.regs i, a.stacks⟩

def leafRegisterPorts : List (Fin 80) := (List.finRange 40).map ABI.leafRegisters

def resetLeafRegisters : Cmd 80 1220 := resetRegisters leafRegisterPorts

def resetLeafState (a : State 80 1220) : State 80 1220 :=
  resetRegisterState leafRegisterPorts a

def loadLeaf : Cmd 80 1220 :=
  .seq clearLeaf (.seq resetLeafRegisters (.seq (clearOutput 1219)
    (.seq (copyWord 265 1104 1219)
      (.seq (copyWord 267 1105 1219) (copyWord 264 1106 1219)))))

def exportLeaf : Cmd 80 1220 :=
  .seq (clearOutput 263) (.seq (clearOutput 1219)
    (.seq (copyWord 1108 263 1219) clearLeaf))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
