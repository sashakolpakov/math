import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace OAI.Algorithms

/-! Canonicalize an arbitrary unary counter by an actual fixed bit loop. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadProgramPrepareCount
open SubexponentialSAT BitProgram StructuredCalls

abbrev program : Program 3 2 6 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code := ![.pop 0 0 1 1,.branch 1 2 4,.set 2 true 3,.push 1 2 0,.set 2 false 5,.halt]

def state (regs : Fin 3 → Bool) (source out : List Bool) : State 3 2 :=
  ⟨regs,![source,out]⟩

theorem trace (regs : Fin 3 → Bool) (source out : List Bool) :
    Trace program (4*source.length+4) ((state regs source out).withPC (some program.entry))
      ((state (fun _ => false) [] (List.replicate source.length true++out)).withPC none) := by
  induction source generalizing regs out with
  | nil =>
    apply Computation.Trace.of_iterate
    simp [Function.iterate_succ_apply,step,program,state,StructuredProgram.State.withPC,execInstr,readRegs]
    funext i; fin_cases i <;> simp
  | cons bit source ih =>
    let next : Fin 3 → Bool := ![bit,true,true]
    have hc : Trace program 4 ((state regs (bit::source) out).withPC (some program.entry))
        ((state next source (true::out)).withPC (some program.entry)) := by
      apply Computation.Trace.of_iterate
      simp [Function.iterate_succ_apply,step,program,state,StructuredProgram.State.withPC,execInstr,readRegs,next]
      constructor <;> (funext i; fin_cases i <;> simp)
    have ht := hc.trans (ih next (true::out))
    convert ht using 1 <;> simp [List.replicate_succ',List.append_assoc] ; omega

end SubexponentialSAT.SqrtLog.PackingHeadProgramPrepareCount

end OAI.Algorithms
