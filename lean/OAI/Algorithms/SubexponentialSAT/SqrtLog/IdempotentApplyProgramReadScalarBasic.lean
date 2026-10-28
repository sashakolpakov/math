import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgramScalar
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramConstant
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramControl

namespace OAI.Algorithms

/-! Scalar loading uses only checked stack primitives and constant formatting.
This definition boundary keeps its correctness independent of polynomial arithmetic. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram
open BitProgram StructuredCalls
open HashCircuitProgram.Native

abbrev sequence (commands : List (Cmd 8 96)) : Cmd 8 96 :=
  commands.foldr Cmd.seq (.base .skip)

def injectPermutation : Equiv.Perm (Fin 96) :=
  (Equiv.swap 1 82).trans ((Equiv.swap 2 83).trans ((Equiv.swap 31 80).trans
    ((Equiv.swap 32 81).trans (Equiv.swap 37 39))))

def injectPorts (i : Fin 41) : Fin 96 := injectPermutation (Fin.castAdd 55 i)

theorem injectPorts_injective : Function.Injective injectPorts :=
  injectPermutation.injective.comp (Fin.castAdd_injective _ _)

abbrev inject : Cmd 8 96 :=
  liftCommand injectScalar 31 32 id injectPorts

def constantPorts (destination : Fin 96) : Fin 6 → Fin 96 :=
  ![89,90,91,81,92,destination]

theorem constantPorts_61_injective : Function.Injective (constantPorts 61) := by decide
theorem constantPorts_67_injective : Function.Injective (constantPorts 67) := by decide

abbrev emitConstant (destination : Fin 96) : Cmd 8 96 :=
  .call (ProgramLinking.liftProgram HashCircuitProgram.Constant.program id
    (constantPorts destination))

/-- Taking a word from the reversed coefficient tape reverses just that word,
so stack80 receives the original forward scalar representation. -/
abbrev readScalar : Cmd 8 96 :=
  .seq (copy 12 82 83)
    (.call (ArrayPrograms.countedTransferProgram 82 79 80 (0 : Fin 8) 1))

abbrev scalarConstant (destination : Fin 96) : Cmd 8 96 := sequence
  [readScalar, inject, clear 80, copy 88 89 70, emitConstant destination]

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
