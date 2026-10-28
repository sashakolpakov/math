import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpConvolutionStore
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Shared native coefficient-ring port allocation. Metadata matches the
scalar CRT services; product operands and output use the convolution ports. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.RingCall
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
def registers : Fin 8 ↪ Fin 16 := ⟨Fin.castAdd 8, Fin.castAdd_injective _ _⟩
def port (i : Fin 32) : Fin 256 :=
  if i = 0 then 200 else if i = 8 then 198 else if i = 9 then 199 else
  if i = 5 then 194 else if i = 12 then 202 else if i = 17 then 203 else
  if i = 22 then 201 else ⟨128+i.val, by omega⟩

theorem port_injective : Function.Injective port := by decide

def ports : Fin 32 ↪ Fin 256 := ⟨port, port_injective⟩

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.RingCall

end OAI.Algorithms
