import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchStorage

namespace OAI.Algorithms

/-! The literal input and output banks of the local-basis batch. -/

namespace SubexponentialSAT.Subexp.LocalBasisBatchProgram

/-- Literal runtime data. The width on 114 is produced by the program. -/
structure Context where
  types : Word
  modulus : Word
  zero : Word
  coefficients : Word
  length : Word
  colors : Word
  positions : Word
  slots : Word
  alphabet : Word

def inputState (ctx : Context) (regs : Fin 32 → Bool) : Data :=
  ⟨regs, fun j =>
    if j = 107 then ctx.types else
    if j = 108 then ctx.modulus else
    if j = 109 then ctx.zero else
    if j = 110 then ctx.coefficients else
    if j = 111 then ctx.length else
    if j = 112 then ctx.colors else
    if j = 113 then ctx.positions else
    if j = 115 then ctx.slots else
    if j = 116 then ctx.alphabet else []⟩

def outputState (ctx : Context) (width result : Word) (regs : Fin 32 → Bool) : Data :=
  ⟨regs, Function.update (Function.update (inputState ctx regs).stacks 114 width) 127 result⟩

end SubexponentialSAT.Subexp.LocalBasisBatchProgram

end OAI.Algorithms
