import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.CounterPrograms
import OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace OAI.Algorithms

/-! Native unary-to-binary conversion for each statistics output. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Binary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
abbrev Data := State 3 3

def state (r : Fin 3 → Bool) (input output : List Bool) : Data :=
  ⟨r,CounterPrograms.lengthStacks input output []⟩
abbrev command : Cmd 3 3 := .seq (.base (.atom (.set 2 false))) (.call CounterPrograms.lengthProgram)
def program := compiled command 0 1

theorem command_eval (r : Fin 3 → Bool) (input : List Bool) :
    ∃ n output, n ≤ input.length*(8*input.length+10)+4 ∧
      BinaryArithmetic.toNat output = input.length ∧ output.length ≤ input.length ∧
      Eval command n (state r input []) (state (fun _ => false) [] output) := by
  obtain ⟨output,hv,hl,n,hn,ht⟩ := CounterPrograms.length_correct_from (r 0) (r 1) input
  have hregs : Function.update r 2 false = CounterPrograms.counterRegs (r 0) (r 1) false := by
    funext i; fin_cases i <;> rfl
  have hreset : Eval (.base (.atom (.set (2 : Fin 3) false))) 1 (state r input [])
      (state (CounterPrograms.counterRegs (r 0) (r 1) false) input []) := by
    have h := Eval.base (StructuredProgram.Eval.atom (.set (2 : Fin 3) false) (state r input []))
    simpa [state,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr,hregs] using h
  have hc : Eval (.call CounterPrograms.lengthProgram) n
      (state (CounterPrograms.counterRegs (r 0) (r 1) false) input [])
      (state (fun _ => false) [] output) := by
    apply Eval.call
    convert ht using 1
    · simp [state,CounterPrograms.lengthCfg,
        StructuredProgram.State.withPC]
    · simp [state,SubexponentialSAT.BitProgram.terminal
        ]
      funext i; fin_cases i <;> rfl
  refine ⟨1+n,output,by omega,(CounterPrograms.value_eq_toNat output).symm.trans hv,hl,hreset.seq hc⟩

theorem program_runsIn (r : Fin 3 → Bool) (input : List Bool) :
    ∃ output, BinaryArithmetic.toNat output = input.length ∧ output.length ≤ input.length ∧
      RunsIn program (input.length*(8*input.length+10)+5)
        ((state r input []).withPC (some program.entry))
        ((state (fun _ => false) [] output).withPC none) := by
  obtain ⟨n,output,hn,hv,hl,he⟩ := command_eval r input
  exact ⟨output,hv,hl,n+1,by omega,compiled_halt_trace he 0 1⟩

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Binary

end OAI.Algorithms
