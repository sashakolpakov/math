import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionHashParameters

namespace OAI.Algorithms

/-! Concrete placement of the selector's numerical preparation in the full
leaf bank. Formula784 and answer787 are outside this routine;782 contains the
actual binary clause count produced by ClauseCount.caller. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.HashParameters

open SubexponentialSAT BitProgram StructuredCalls

def registers (i : Fin 16) : Fin 40 := i.castAdd 24

def stackMap : Fin 44 → Fin 896 :=
  ![768,769,770,771,772,773,774,775,776,777,778,779,780,781,
    785,782,786,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26]

def ports : Execution.HashParameters.Ports 40 896 :=
  ⟨registers,stackMap,Fin.castAdd_injective 16 24,by decide⟩

abbrev command : Cmd 40 896 := Execution.HashParameters.command ports

abbrev withSelector (mass : Cmd 40 896) : Cmd 40 896 :=
  Execution.HashParameters.withSelector ports mass

@[simp] theorem ambient_port : ports.stack 14 = 785 := rfl
@[simp] theorem clauses_port : ports.stack 15 = 782 := rfl
@[simp] theorem occurrence_port : ports.stack 16 = 786 := rfl
@[simp] theorem rows_port : ports.hash.stack 9 = 777 := rfl
@[simp] theorem alphabet_port : ports.hash.stack 0 = 768 := rfl
@[simp] theorem depth_port : ports.hash.stack 5 = 773 := rfl
@[simp] theorem rounds_port : ports.hash.stack 6 = 774 := rfl

/-- The exact fixed mapping reuses the already measured native arithmetic;
no code, field, or formula-dependent program is constructed here. -/
theorem command_eval (a : State 40 896) (L : ℕ)
    (hword : SubexpSetupStorage.WordBound L (projectState ports.register ports.stack a))
    (hready : Execution.HashInputs.Ready (projectState ports.hash.register ports.hash.stack a))
    (hm : BinaryArithmetic.toNat (a.stacks 782) ≠ 0) :
    ∃ t ≤ 10000000000*(L+1)^2+1, ∃ b : State 40 896,
      Eval command t a b ∧
      Execution.HashInputs.Ready (projectState ports.hash.register ports.hash.stack b) ∧
      BinaryArithmetic.toNat (b.stacks 768) = 3*BinaryArithmetic.toNat (a.stacks 782) ∧
      BinaryArithmetic.toNat (b.stacks 773) = SparseCode.distanceDenom
        (BinaryArithmetic.toNat (a.stacks 782)) (BinaryArithmetic.toNat (a.stacks 786)) ∧
      BinaryArithmetic.toNat (b.stacks 774) = HashSelect.loopCap
        (BinaryArithmetic.toNat (a.stacks 785)) (BinaryArithmetic.toNat (a.stacks 782)) ∧
      b.stacks 777 = a.stacks 777 := by
  obtain ⟨t,ht,b,he,hr,h0,h5,h6,h9,_⟩ :=
    Execution.HashParameters.command_eval ports a L hword hready hm
  exact ⟨t,ht,b,he,hr,h0,h5,h6,h9⟩

end SubexponentialSAT.SqrtLog.LeafProgram.HashParameters

end OAI.Algorithms
