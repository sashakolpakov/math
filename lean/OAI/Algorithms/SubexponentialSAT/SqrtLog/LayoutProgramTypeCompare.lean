import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstraintEntryCompare

namespace OAI.Algorithms

/-! Preserving comparison of the two type words using scratch0..3. All cache
ports42..48 remain intact. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.TypeCompare

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

abbrev Data := State 10 64

def ports : Fin 46 → Fin 64 :=
  ![42,43,44,45,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,
    25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,0,1,2,3]

theorem ports_inj : Function.Injective ports := by decide

abbrev command : Cmd 10 64 := liftCommand ConstraintEntryCompare.command 23 23 id ports

theorem command_eval (a : Data) (h0 : a.stacks 0=[]) (h1 : a.stacks 1=[])
    (h2 : a.stacks 2=[]) (h3 : a.stacks 3=[]) :
    ∃ n ≤ 18*(a.stacks 23).length+9*(a.stacks 24).length+34,
      ∃ e : Data, Eval command n a e ∧ e.stacks=a.stacks ∧
        e.regs 7=decide (a.stacks 23=a.stacks 24) := by
  let p := projectState id ports a
  obtain ⟨n,hn,rr,he,hr⟩ := ConstraintEntryCompare.command_eval p h0 h1 h2 h3
  let e := embedState id ports a ⟨rr,p.stacks⟩
  have hh := eval_liftCommand_from_state ConstraintEntryCompare.command 23 23 id ports a
    Function.injective_id ports_inj he
  have hs : e.stacks=a.stacks := by
    change Function.extend ports p.stacks a.stacks=a.stacks
    exact congrArg StructuredProgram.State.stacks (embedState_project id ports a Function.injective_id ports_inj)
  have h7 : e.regs 7=rr 7 :=
    embedState_register id ports a ⟨rr,p.stacks⟩ Function.injective_id 7
  refine ⟨n+1,?_,e,hh,hs,?_⟩
  · simpa [p,projectState,ports] using Nat.add_le_add_right hn 1
  · simpa [p,projectState,ports] using h7.trans hr

end SubexponentialSAT.SqrtLog.LayoutProgram.TypeCompare

end OAI.Algorithms
