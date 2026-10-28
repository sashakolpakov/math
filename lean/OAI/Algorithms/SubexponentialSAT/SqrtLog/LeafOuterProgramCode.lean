import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramSearchCode
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramDispatch
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramClauseCount
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramPrepareCode
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramDecision
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramCode

namespace OAI.Algorithms

/-! The complete outer leaf instruction table. The two remaining arguments
are actual native commands for the mass and final accepted-count services.
All setup, code search, serialization, selector iteration and positivity
testing below are fixed programs, independent of the input dimensions. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram

open SubexponentialSAT BitProgram StructuredCalls

def rowInputs : List Route :=
  [(801,3),(782,4),(768,5),(808,6),(809,7),(814,8),(816,9),(815,10),(812,11)]
def rowOutputs : List Route := [(12,777)]
abbrev serialize : Cmd 40 896 :=
  stage rowInputs CodeRowsProgram.program regs16 stacks64 rowOutputs

abbrev constructCode : Cmd 40 896 :=
  .seq parameters (.seq localCode (.seq graphCode serialize))

def decisionRegisters : Fin 2 → Fin 40 := Fin.castAdd 38
def decisionStacks : Fin 2 → Fin 896 := ![788,787]
abbrev decideCount : Cmd 40 896 :=
  .call (ProgramLinking.liftProgram LeafProgram.Decision.program decisionRegisters decisionStacks)

abbrev start : Cmd 40 896 :=
  .seq LeafProgram.ClauseCount.caller (.seq prepareHash saveWidth)

/-- The final-count service places its binary answer in outer tape788. The
mass service follows the actual selector core's fixed tape protocol. -/
abbrev nontrivial (mass acceptedCount : Cmd 40 896) : Cmd 40 896 :=
  .seq start <|
  .seq constructCode <|
  .seq (Execution.Hash.command LeafProgram.HashParameters.ports.hash mass) <|
  .seq acceptedCount decideCount

abbrev command (mass acceptedCount : Cmd 40 896) : Cmd 40 896 :=
  LeafProgram.Dispatch.command (nontrivial mass acceptedCount)

abbrev program (mass acceptedCount : Cmd 40 896) := compiled (command mass acceptedCount) 784 787

theorem rowInputs_valid : ∀ p ∈ rowInputs, routeValid p := by
  intro p hp
  simp only [rowInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals unfold routeValid; decide
theorem rowOutputs_valid : ∀ p ∈ rowOutputs, routeValid p := by
  intro p hp
  simp only [rowOutputs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl
  all_goals unfold routeValid; decide

theorem primitive_run (mass acceptedCount : Cmd 40 896) {a b : Data} {n : ℕ}
    (h : Eval (command mass acceptedCount) n a b) :
    Computation.RunsIn (primitive (program mass acceptedCount)).step
      (primitiveOverhead (program mass acceptedCount)*(n+1))
      (primitiveCfg (program mass acceptedCount) (a.withPC (some (program mass acceptedCount).entry)))
      (primitiveCfg (program mass acceptedCount) (b.withPC none)) := by
  exact BitProgram.primitive_execution (program mass acceptedCount)
    ⟨n+1,le_rfl,compiled_halt_trace h 784 787⟩

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
