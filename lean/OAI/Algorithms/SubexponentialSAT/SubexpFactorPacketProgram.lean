import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFactorPacketControl
import OAI.Algorithms.SubexponentialSAT.SubexpFactorPrefixControl

namespace OAI.Algorithms

/-!
# Physical original-order factor-packet stage

The current-node origins227 are consumed by the scope-prefix constructor.
Its temporary grouped stream224 is consumed by the outer packet stage and
then cleared. The final packets are on225. All input masters are physically
read through the native programs' copied cursors.
-/

namespace SubexponentialSAT.SubexpFactorPacketProgram

open BitProgram StructuredCalls

abbrev Data := State 16 288

def registers : Fin 8 → Fin 16 := Fin.castAdd 8

def prefixPorts (i : Fin 24) : Fin 288 :=
  if i = 0 then 227 else if i = 1 then 102 else if i = 2 then 256
  else if i = 3 then 224 else ⟨134 + i.val, by omega⟩

def packetPorts (i : Fin 64) : Fin 288 :=
  if i = 40 then 284 else if i = 41 then 224 else if i = 42 then 257
  else if i = 43 then 128 else if i = 44 then 119 else if i = 45 then 120
  else if i = 47 then 225 else ⟨138 + i.val, by omega⟩

theorem registers_injective : Function.Injective registers := Fin.castAdd_injective _ _
theorem prefixPorts_injective : Function.Injective prefixPorts := by decide
theorem packetPorts_injective : Function.Injective packetPorts := by decide

abbrev prefixes : Cmd 16 288 := .call
  (ProgramLinking.liftProgram SubexpFactorPrefixProgram.program registers prefixPorts)
abbrev packets : Cmd 16 288 := .call
  (ProgramLinking.liftProgram SubexpFactorPacketControl.program registers packetPorts)
abbrev cleanup : Cmd 16 288 := .call (StackRoutines.clearProgram 224 0 1)
abbrev command : Cmd 16 288 := .seq prefixes (.seq packets cleanup)
def program := compiled command (102 : Fin 288) 225

end SubexponentialSAT.SubexpFactorPacketProgram

end OAI.Algorithms
