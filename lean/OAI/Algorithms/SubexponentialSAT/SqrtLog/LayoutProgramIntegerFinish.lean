import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramUniversalEntry
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramTypeCompare

namespace OAI.Algorithms

/-! Final physical defect conversion, preserving all caller inputs and
removing the temporary numerator pair. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.IntegerFinish

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp RowSelectionProgram
open UniversalEntry

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Data := State 10 64

abbrev command : Cmd 10 64 := .seq defect clearNumerator

def Ready (a : Data) : Prop := ∀ j : Fin 64, j∈[53,54,0,1,4,5,6] → a.stacks j=[]
def output (a : Data) (p n : List Bool) : Fin 64 → List Bool :=
  Function.update (Function.update (Function.update (Function.update a.stacks 53 p) 54 n) 50 []) 51 []

def budget (a : Data) : ℕ :=
  9*(a.stacks 50).length+2*(a.stacks 51).length+
    100*((a.stacks 51).length+(a.stacks 45).length+1)^2+19

theorem command_eval (a : Data) (ha : Ready a) :
    ∃ t ≤ budget a, ∃ e p n, Eval command t a e ∧ e.stacks=output a p n ∧
      (BinaryArithmetic.toNat p : ℤ)-BinaryArithmetic.toNat n =
        (if a.regs 7 then (BinaryArithmetic.toNat (a.stacks 45):ℤ) else 0)-
          ((BinaryArithmetic.toNat (a.stacks 50):ℤ)-BinaryArithmetic.toNat (a.stacks 51)) ∧
      BinaryArithmetic.toNat p+BinaryArithmetic.toNat n=
        BinaryArithmetic.toNat (a.stacks 50)+BinaryArithmetic.toNat (a.stacks 51)+
          (if a.regs 7 then BinaryArithmetic.toNat (a.stacks 45) else 0) ∧
      p.length+n.length ≤ (a.stacks 50).length+(a.stacks 51).length+(a.stacks 45).length+1 := by
  let d := projectState smallRegs defectPorts a
  have hd : Defect.Ready d := by
    intro j hj
    fin_cases j <;> simp_all [d,projectState,defectPorts,Ready]
  obtain ⟨nd,hnd,rd,p,n,hdone,hvalue,hmass,hlen⟩ := Defect.command_eval d hd
  let m := embedState smallRegs defectPorts a ⟨rd,Defect.output d p n⟩
  have he := eval_liftCommand_from_state Defect.command 0 3 smallRegs defectPorts a
    smallRegs_inj defectPorts_inj hdone
  have hms : m.stacks=Function.update (Function.update a.stacks 54 n) 53 p := by
    change Function.extend defectPorts (Defect.output d p n) a.stacks = _
    unfold Defect.output
    rw [ProgramLinking.extend_update defectPorts_inj,ProgramLinking.extend_update defectPorts_inj]
    have hb := congrArg StructuredProgram.State.stacks
      (embedState_project smallRegs defectPorts a smallRegs_inj defectPorts_inj)
    change Function.extend defectPorts d.stacks a.stacks=a.stacks at hb
    rw [hb]
    rfl
  let s₁ : Data := ⟨readRegs m.regs 0 1 none,StackRoutines.clearStacks 50 m.stacks⟩
  let e : Data := ⟨readRegs s₁.regs 0 1 none,StackRoutines.clearStacks 51 s₁.stacks⟩
  have h₁ := Subexp.TupleProgram.clear_eval 50 0 1 m
  have h₂ := Subexp.TupleProgram.clear_eval 51 0 1 s₁
  have hout : e.stacks=output a p n := by
    funext j
    by_cases h50 : j=50 <;> by_cases h51 : j=51 <;> by_cases h53 : j=53 <;>
      by_cases h54 : j=54 <;> simp_all [e,s₁,StackRoutines.clearStacks,output]
  have hrun : Eval command ((nd+1)+(2*(m.stacks 50).length+3+(2*(s₁.stacks 51).length+3))) a e :=
    he.seq (h₁.seq h₂)
  refine ⟨_,?_,e,p,n,hrun,hout,?_,?_,?_⟩
  · simp [d,projectState,defectPorts,Defect.budget] at hnd
    simp [budget,s₁,StackRoutines.clearStacks,hms]
    omega
  · simpa [d,projectState,defectPorts,smallRegs] using hvalue
  · simpa [d,projectState,defectPorts,smallRegs] using hmass
  · simpa [d,projectState,defectPorts] using hlen

end SubexponentialSAT.SqrtLog.LayoutProgram.IntegerFinish

end OAI.Algorithms
