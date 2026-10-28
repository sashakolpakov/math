import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgramMassBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgramPrepareUtil

namespace OAI.Algorithms

/-! Preserving wrapper around the actual nested record counter. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.MassPreserve
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 8 5
abbrev Code := Cmd 8 5
def state (regs : Fin 8 → Bool) (source acc : List Bool) : Data :=
  ⟨regs, ![source, [], acc, [], []]⟩
def regs : Fin 5 → Fin 8 := Fin.castAdd 3
def stackPorts : Fin 4 → Fin 5 := ![4, 1, 2, 3]
theorem regs_injective : Function.Injective regs := Fin.castAdd_injective _ _
theorem stackPorts_injective : Function.Injective stackPorts := by decide

def reset : Code := .seq (.base (.atom (.set 2 false)))
  (.seq (.base (.atom (.set 3 true))) (.base (.atom (.set 4 false))))
def resetRegs (r : Fin 8 → Bool) :=
  Function.update (Function.update (Function.update r 2 false) 3 true) 4 false
theorem reset_eval (d : Data) :
    Eval reset 3 d ⟨resetRegs d.regs, d.stacks⟩ :=
  (Eval.base (.atom _ _)).seq ((Eval.base (.atom _ _)).seq (Eval.base (.atom _ _)))

def command : Code := .seq (ArithmeticCalls.copyAt 0 4 3)
  (.seq reset (.call (ProgramLinking.liftProgram Mass.program regs stackPorts)))
def program := compiled command 0 2
def bound (source : List Bool) := 35 * (source.length + 1) + 4

theorem command_eval (r : Fin 8 → Bool) (scopes : List (List ℕ)) :
    ∃ time rf, Eval command time
      (state r (SubexpIncidenceSlotProgram.scopeBits scopes) [])
      (state rf (SubexpIncidenceSlotProgram.scopeBits scopes)
        (List.replicate ((scopes.map List.length).sum) true)) ∧
      time + 1 ≤ bound (SubexpIncidenceSlotProgram.scopeBits scopes) := by
  let source := SubexpIncidenceSlotProgram.scopeBits scopes
  let a := state r source []
  let copied := ArithmeticCalls.afterCopy 0 4 a
  let ready : Data := ⟨resetRegs copied.regs, copied.stacks⟩
  have hc := ArithmeticCalls.copyAt_eval (0 : Fin 5) 4 3 a
    (by decide) (by decide) (by decide) (by rfl) (by rfl)
  have hp : projectState regs stackPorts ready =
      RecordPrograms.state Mass.ports (Mass.state (ready.regs ∘ regs) [] [] [] [])
        false true false source [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  obtain ⟨rf, time, ht, he⟩ := Mass.scopes_runsIn (ready.regs ∘ regs) scopes
  rw [← hp] at he
  let out := Mass.state rf [] [] (List.replicate ((scopes.map List.length).sum) true) []
  let b := embedState regs stackPorts ready out
  have hm := eval_call_from_state Mass.program regs stackPorts ready
    regs_injective stackPorts_injective he
  have hs (i : Fin 4) : b.stacks (stackPorts i) = out.stacks i :=
    embedState_stack _ _ _ _ stackPorts_injective i
  have hb : b = state b.regs source (List.replicate ((scopes.map List.length).sum) true) := by
    apply congrArg (StructuredProgram.State.mk b.regs)
    funext i
    fin_cases i
    · exact embedState_stack_frame regs stackPorts ready out 0 (by decide)
    · exact hs 1
    · exact hs 2
    · exact hs 3
    · exact hs 0
  change Eval _ _ ready b at hm
  rw [hb] at hm
  refine ⟨(7 * source.length + 5) + (3 + time), b.regs,
    hc.seq ((reset_eval copied).seq hm), ?_⟩
  dsimp [bound, source]
  omega

theorem runsIn (r : Fin 8 → Bool) (scopes : List (List ℕ)) :
    ∃ rf, RunsIn program (bound (SubexpIncidenceSlotProgram.scopeBits scopes))
      ((state r (SubexpIncidenceSlotProgram.scopeBits scopes) []).withPC (some program.entry))
      ((state rf (SubexpIncidenceSlotProgram.scopeBits scopes)
        (List.replicate ((scopes.map List.length).sum) true)).withPC none) := by
  obtain ⟨time, rf, he, ht⟩ := command_eval r scopes
  exact ⟨rf, time + 1, ht, compiled_halt_trace he 0 2⟩

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.MassPreserve

end OAI.Algorithms
