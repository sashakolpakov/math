import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendParameterCall
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendScopeCall
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgramLowMask
import OAI.Algorithms.SubexponentialSAT.ArithmeticExpressionSupport

namespace OAI.Algorithms

/-! Fixed native syntax from physical formula/row masters through the guarded
parameter bank. The only static input is the fixed formula-width bound k. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

def sequence : List Code → Code
  | [] => .base .skip
  | c::cs => .seq c (sequence cs)

def loadBits (dst : Fin 768) (bits : List Bool) : Code :=
  liftCommand (ArithmeticExpressionSupport.pushWord dst bits) dst dst r8 id

def scopeCopies : List (Fin 768 × Fin 768) :=
  [(700,514),(701,546),(705,549),(706,550),(707,507),(708,501)]
def resetScopeRegs : Code := setRegs [.set 0 false,.set 1 false,.set 2 false,.set 3 false,.set 4 false,
  .set 5 false,.set 6 false,.set 7 false,.set 8 false,.set 9 false,.set 10 false]
def prepareScopes : Code := sequence [copies scopeCopies,loadBits 515 [false,false],resetScopeRegs]

def highCopies : List (Fin 768 × Fin 768) := [(718,580),(709,596),(433,597)]
def statsCopies : List (Fin 768 × Fin 768) := [(718,612),(719,632)]
def arityCopies : List (Fin 768 × Fin 768) := [(719,633),(718,640)]
def arityRegisters : Code := setRegs [.set 7 false,.set 8 true,.set 9 false]

def binaryPorts (src dst : Fin 768) : Fin 3 → Fin 768 := ![src,dst,647]
def binary (src dst : Fin 768) : Code :=
  .call (ProgramLinking.liftProgram LeafStatisticsProgram.Binary.program r3 (binaryPorts src dst))

def countPorts : Fin 2 → Fin 768 := ![647,704]
def countHashes : Code := sequence [copy 701 647,
  .call (ProgramLinking.liftProgram SubexpScopeCountSetup.counterProgram r2 countPorts)]

/-- Metadata k is fixed for the width-k solver and is loaded by paid bit pushes.
Every other numeric input is either a retained master or a physical scan output. -/
def numericInputs (k : ℕ) : Code := sequence [
  copies [(709,340),(707,342)], loadBits 346 k.bits,
  binary 626 341, binary 627 343, binary 642 344,
  binary 613 345, binary 628 347]

def command (k : ℕ) : Code := sequence [
  countHashes, prepareScopes, scopeCall, copy 546 718,
  copy 709 417, earlyCall, copies highCopies, highCall, copy 594 338,
  maskCall, copies statsCopies, statsCall,
  copies arityCopies, arityRegisters, arityCall, finishCall,
  numericInputs k, parameterCall]

def offsetPorts : Fin 22 → Fin 768 :=
  ![725,720,727,650,651,652,653,654,655,141,656,657,658,659,660,661,662,663,664,665,666,667]
def offsetCall : Code := .call (ProgramLinking.liftProgram LayoutOffsetProgram.program r8 offsetPorts)
def lowPorts : Fin 2 → Fin 768 := ![668,134]
def lowCall : Code := .call (ProgramLinking.liftProgram HeadIdentifierProgram.LowMask.program r2 lowPorts)
def lowMask : Code := .seq (copy 338 668) lowCall

def program (k : ℕ) := compiled (command k) 700 382

theorem binaryPorts_injective (src dst : Fin 768) (hsd : src≠dst)
    (hs : src≠647) (hd : dst≠647) : Function.Injective (binaryPorts src dst) := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [binaryPorts]
theorem offsetPorts_injective : Function.Injective offsetPorts := by decide
theorem lowPorts_injective : Function.Injective lowPorts := by decide
theorem countPorts_injective : Function.Injective countPorts := by decide

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
