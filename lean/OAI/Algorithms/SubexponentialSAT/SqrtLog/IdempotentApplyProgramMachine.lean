import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgramReadScalarBasic
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgramScalar
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgramAdd
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramArithmeticNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramConstant
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeKeyMapProgram

namespace OAI.Algorithms

/-! Fixed native control for applying computed idempotent coefficients.
The input and output ABI is documented below. The semantic execution theorem
is a separate obligation; this module supplies concrete instructions only. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

open BitProgram StructuredCalls
open HashCircuitProgram.Native

def uKeyPorts : Fin 6 → Fin 96 := ![89,90,91,81,92,93]

theorem uKeyPorts_injective : Function.Injective uKeyPorts := by decide

abbrev makeUKey : Cmd 8 96 := sequence
  [copy 88 89 70,
   liftCommand HashCircuitProgram.Constant.pad 0 2 id uKeyPorts,
   liftCommand HashCircuitProgram.Constant.tag 2 2 id uKeyPorts,
   .base (.atom (.set 0 true)), .base (.atom (.push 91 0)),
   copy 91 94 70, clear 91]

def shiftPorts : Fin 15 → Fin 96 :=
  ![67,94,45,46,86,80,81,82,83,84,85,89,90,91,92]

theorem shiftPorts_injective : Function.Injective shiftPorts := by decide

abbrev shiftU : Cmd 8 96 :=
  .call (ProgramLinking.liftProgram Squarefree.KeyMapProgram.scanProgram id shiftPorts)

/-- H(H-1)(H-2)=H(1-H)(2-H). The latter form reuses the checked native
complement service, whose cached constants are ordinary ring data. -/
abbrev prepareMultiplier : Cmd 8 96 := sequence
  [copy 68 61 70, complement,
   copy 61 85 70, copy 61 67 70, clear 61,
   copy 69 61 70, add,
   copy 85 61 70, productAdapter product, clear 85,
   copy 68 61 70, productAdapter product,
   makeUKey, shiftU]

abbrev peekCoefficients : Cmd 8 96 := .base (.atom (.peek 79 0 7))

/-- Two products and two sums evaluate one quadratic coefficient digit. -/
abbrev tripleStep : Cmd 8 96 := sequence
  [scalarConstant 67,
   copy 68 61 70, productAdapter product,
   scalarConstant 61, add,
   copy 68 61 70, productAdapter product,
   scalarConstant 61, add]

abbrev accumulatorStep : Cmd 8 96 := sequence
  [copy 67 85 70, clear 67,
   copy 87 67 70, clear 87,
   copy 86 61 70, productAdapter product,
   copy 85 61 70, clear 85, add,
   copy 67 87 70, clear 67]

/-- Exactly three scalar loads, three polynomial products and three sums.
The coefficient order is c,b,a because the whole coefficient tape is reversed. -/
abbrev hornerStep : Cmd 8 96 := .seq tripleStep (.seq accumulatorStep peekCoefficients)

/-- Input68 is raw H;78 holds the forward computed coefficient tape;88 is
an ambient shape word. Cached one69 and minus-one76 and the low56 product
environment are preserved. Output67 is the raw indicator dictionary. Scratch
61,70,79..87,89..95 must be empty initially and is reclaimed before return. -/
noncomputable def command : Cmd 8 96 := sequence
  [prepareMultiplier,
   copy 78 84 70, transfer 84 79, peekCoefficients,
   .while 7 hornerStep,
   copy 87 67 70, clear 87, clear 86, clear 94]

noncomputable def program : Program 8 96 (size command + 1) := compiled command 68 67

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
