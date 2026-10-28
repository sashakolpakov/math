import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SetupPrimitives
import OAI.Algorithms.SubexponentialSAT.SubexpBlockParameterProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCodeParameters
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramBounds

namespace OAI.Algorithms

/-! Native logarithmic component of the hash-parameter setup. -/
namespace SubexponentialSAT.SqrtLog.HashParametersProgram

open BitProgram StructuredCalls BinaryArithmetic SubexpBlockParameterProgram

abbrev resetLog : Cmd 3 3 := .base (SubexpParameterProgram.atoms
  [.set 0 false, .set 1 false, .set 2 false])

abbrev logCommand : Cmd 3 3 := .seq resetLog Setup.logSucc

theorem logCommand_eval (xs : List Bool) (d : State 3 3)
    (hs : d.stacks = (Setup.io xs).stacks) :
    ∃ output t, BinaryArithmetic.toNat output = SparseCode.logSize (BinaryArithmetic.toNat xs) ∧
      output.length ≤ xs.length+1 ∧ t ≤ 35*(xs.length+1)^2 ∧
      Eval logCommand t d (Setup.io output) := by
  have hr := SubexpParameterProgram.atoms_eval
    ([.set 0 false, .set 1 false, .set 2 false] : List (StructuredProgram.Atom 3 3)) d
  have hh : SubexpParameterProgram.runAtoms
      [.set 0 false, .set 1 false, .set 2 false] d = Setup.io xs := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> rfl
    · exact hs
  obtain ⟨output,t,hv,hl,ht,he⟩ := Setup.logSucc_eval xs
  refine ⟨output,3+t,?_,hl,by nlinarith,.seq (.base (hh ▸ hr)) he⟩
  simpa only [SubexpParameterProgram.value_eq_toNat, SparseCode.logSize, Nat.log2_eq_log_two] using hv

def logRegisters : Fin 3 → Fin 8 := Fin.castAdd 5
def logStacks : Fin 3 → Fin 22 := ![3,15,16]
abbrev logCall : Cmd 8 22 := liftCommand logCommand 0 0 logRegisters logStacks

theorem logCall_eval (r : Regs) (w : Words) :
    ∃ t rf output,
      Eval logCall t (state r w) (state rf (Function.update w 3 output)) ∧
      BinaryArithmetic.toNat output = SparseCode.logSize (BinaryArithmetic.toNat (w 3)) ∧
      output.length ≤ (w 3).length+1 ∧ t ≤ 36*((w 3).length+1)^2 := by
  have hi : Function.Injective logRegisters := Fin.castAdd_injective _ _
  have hj : Function.Injective logStacks := by decide
  let d := state r w
  have hs : (projectState logRegisters logStacks d).stacks = (Setup.io (w 3)).stacks := by
    funext i
    fin_cases i
    · change (state r w).stacks (port 3) = w 3
      exact state_port r w 3
    · change (state r w).stacks (15 : Fin 22) = []
      exact state_work r w 15 (by decide)
    · change (state r w).stacks (16 : Fin 22) = []
      exact state_work r w 16 (by decide)
  obtain ⟨output,t,hv,hl,ht,he⟩ := logCommand_eval (w 3)
    (projectState logRegisters logStacks d) hs
  let e := embedState logRegisters logStacks d (Setup.io output)
  have hr : Eval logCall (t+1) d e :=
    eval_liftCommand_from_state logCommand 0 0 logRegisters logStacks d hi hj he
  have hw : (Setup.io output).stacks =
      Function.update (projectState logRegisters logStacks d).stacks 0 output := by
    rw [hs]; funext i; fin_cases i <;> simp []
  have hse : e.stacks = Function.update d.stacks 3 output := by
    change Function.extend logStacks (Setup.io output).stacks d.stacks = _
    rw [hw,ProgramLinking.extend_update hj]
    have hx := congrArg StructuredProgram.State.stacks (embedState_project logRegisters logStacks d hi hj)
    change Function.extend logStacks (projectState logRegisters logStacks d).stacks d.stacks = d.stacks at hx
    rw [hx]; rfl
  have heq : e = state e.regs (Function.update w 3 output) := by
    rw [← state_update r e.regs w 3 output]
    exact CounterForPrograms.data_ext rfl hse
  refine ⟨t+1,e.regs,output,?_,hv,hl,by nlinarith⟩
  rw [← heq]
  exact hr

abbrev copyClause : Cmd 8 22 := ArithmeticExpressionSupport.copyCmd 1 3 21

theorem copyClause_eval (r : Regs) (w : Words) (h3 : w 3 = []) :
    Eval copyClause (7*(w 1).length+5) (state r w)
      (state (readRegs r 0 1 none) (Function.update w 3 (w 1))) := by
  have h := ArithmeticExpressionSupport.copy_eval (port 1) (port 3) 21 (state r w)
    (by decide) (by decide) (by decide)
    (by simpa only [state_port] using h3) (state_work r w 21 (by decide))
  simp only [state_port] at h
  rw [state_update] at h
  exact h

end SubexponentialSAT.SqrtLog.HashParametersProgram

end OAI.Algorithms
