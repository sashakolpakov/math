import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeTemplateStage
import OAI.Algorithms.SubexponentialSAT.SubexpTemplateExecution

namespace OAI.Algorithms

/-! The actual native template traversal, placed in the node workspace and
followed by the physical cache cleanup. The only semantic inputs are the
decoded raw blocks and the arithmetic context; no execution callback is
assumed. -/

namespace SubexponentialSAT.SubexpNodeTemplateExecution

open BitProgram StructuredCalls SubexpSelectedConversions
open SubexpTemplateProgram
open SubexpNodeTemplateStage (localState registers port)

abbrev Data := SubexpNodeTemplateStage.Data

theorem native_stacks (ctx : Context) (regs rf : Fin 8 → Bool)
    (input output : List Bool) :
    (state ctx rf {output := output}).stacks =
      Function.update (Function.update (serviceState ctx regs input).stacks 130 []) 139 output := by
  funext i
  by_cases h130 : i = 130
  · subst i
    simp [serviceState, state_stack_eq]
  · by_cases h139 : i = 139
    · subst i
      simp [serviceState, state_stack_eq]
    · simp [serviceState, state_stack_eq, h130, h139]

theorem embedded_stacks (d : Data) (out : SubexpTemplateProgram.Data) (output : List Bool)
    (h : out.stacks =
      Function.update (Function.update (localState d).stacks 130 []) 139 output) :
    (embedState registers port d out).stacks =
      Function.update (Function.update d.stacks 15 []) 200 output := by
  change Function.extend port out.stacks d.stacks = _
  rw [h, ProgramLinking.extend_update SubexpNodeTemplateStage.port_injective,
    ProgramLinking.extend_update SubexpNodeTemplateStage.port_injective]
  have hb := congrArg StructuredProgram.State.stacks
    (SubexpNodeTemplateStage.localState_embed d)
  change Function.extend port (localState d).stacks d.stacks = d.stacks at hb
  rw [hb, SubexpNodeTemplateStage.port_input, SubexpNodeTemplateStage.port_output]

def finishedStacks (s : Fin 256 → List Bool) (output : List Bool) : Fin 256 → List Bool :=
  fun i => if i ∈ SubexpNodeCacheSetup.cleanupPorts then []
    else Function.update (Function.update s 15 []) 200 output i

theorem cleanup_cost (d : Data) (out : SubexpTemplateProgram.Data) (output : List Bool)
    (h : out.stacks =
      Function.update (Function.update (localState d).stacks 130 []) 139 output) :
    SubexpNodeCacheSetup.cleanupCost (embedState registers port d out) =
      SubexpNodeCacheSetup.cleanupCost d := by
  have hs := embedded_stacks d out output h
  simp only [SubexpNodeCacheSetup.cleanupCost, hs]
  simp

theorem finished_stacks (d : Data) (out : SubexpTemplateProgram.Data) (output : List Bool)
    (h : out.stacks =
      Function.update (Function.update (localState d).stacks 130 []) 139 output) :
    (SubexpNodeCacheSetup.cleared SubexpNodeCacheSetup.cleanupPorts
      (embedState registers port d out)).stacks = finishedStacks d.stacks output := by
  funext i
  simp only [SubexpNodeCacheSetup.cleared_stacks, embedded_stacks d out output h,
    finishedStacks]

@[simp] theorem finished_output (s : Fin 256 → List Bool) (output : List Bool) :
    finishedStacks s output 200 = output := by
  simp [finishedStacks, SubexpNodeCacheSetup.cleanupPorts]

@[simp] theorem finished_input (s : Fin 256 → List Bool) (output : List Bool) :
    finishedStacks s output 15 = [] := by
  simp [finishedStacks, SubexpNodeCacheSetup.cleanupPorts]

theorem finished_frame (s : Fin 256 → List Bool) (output : List Bool) (i : Fin 256)
    (hi : i ∉ SubexpNodeCacheSetup.cleanupPorts) (h15 : i ≠ 15) (h200 : i ≠ 200) :
    finishedStacks s output i = s i := by
  simp [finishedStacks, hi, h15, h200]

variable {p D : ℕ} [Fact p.Prime]

theorem command_eval (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (hc : SubexpTemplateData.ContextGood ctx source target minusOne)
    (bs : List (SubexpTemplateData.Block p D)) (d : Data)
    (hi : localState d = serviceState ctx (localState d).regs
      (SubexpTemplateProgram.encodeBlocks (bs.map SubexpTemplateData.rawBlock))) :
    ∃ n ≤ SubexpTemplateExecution.runCost ctx source target minusOne bs +
        SubexpNodeCacheSetup.cleanupCost d, ∃ out : Data,
      Eval SubexpNodeTemplateStage.command n d out ∧
      out.stacks = finishedStacks d.stacks
        (SubexpTemplateExecution.output ctx source target minusOne bs) := by
  obtain ⟨rf,n,hn,ht⟩ := SubexpTemplateExecution.program_runsIn
    ctx source target minusOne hc bs (localState d).regs
  let e := state ctx rf {output := SubexpTemplateExecution.output ctx source target minusOne bs}
  have he : e.stacks = Function.update
      (Function.update (localState d).stacks 130 []) 139
      (SubexpTemplateExecution.output ctx source target minusOne bs) := by
    rw [hi]
    exact native_stacks ctx _ rf _ _
  have htrace : Trace SubexpTemplateProgram.program n
      ((localState d).withPC (some SubexpTemplateProgram.program.entry)) (e.withPC none) := by
    rw [hi]
    exact ht
  have hcst := cleanup_cost d e _ he
  refine ⟨n + SubexpNodeCacheSetup.cleanupCost (embedState registers port d e), ?_,
    SubexpNodeCacheSetup.cleared SubexpNodeCacheSetup.cleanupPorts
      (embedState registers port d e),
    SubexpNodeTemplateStage.command_eval_from_trace d e n htrace,
    finished_stacks d e _ he⟩
  rw [hcst]
  omega

theorem program_runs (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (hc : SubexpTemplateData.ContextGood ctx source target minusOne)
    (bs : List (SubexpTemplateData.Block p D)) (d : Data)
    (hi : localState d = serviceState ctx (localState d).regs
      (SubexpTemplateProgram.encodeBlocks (bs.map SubexpTemplateData.rawBlock))) :
    ∃ out : Data, RunsIn SubexpNodeTemplateStage.program
        (SubexpTemplateExecution.runCost ctx source target minusOne bs +
          SubexpNodeCacheSetup.cleanupCost d + 1)
        (d.withPC (some SubexpNodeTemplateStage.program.entry)) (out.withPC none) ∧
      out.stacks = finishedStacks d.stacks
        (SubexpTemplateExecution.output ctx source target minusOne bs) := by
  obtain ⟨n,hn,out,he,hs⟩ := command_eval ctx source target minusOne hc bs d hi
  exact ⟨out,⟨n+1,Nat.add_le_add_right hn 1,compiled_halt_trace he 15 200⟩,hs⟩

end SubexponentialSAT.SubexpNodeTemplateExecution

end OAI.Algorithms
