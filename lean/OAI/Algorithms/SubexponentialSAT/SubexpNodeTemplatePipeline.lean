import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeTemplateExecution
import OAI.Algorithms.SubexponentialSAT.SubexpNodeTemplateReady
import OAI.Algorithms.SubexponentialSAT.SubexpNodeWidePipeline

namespace OAI.Algorithms

/-! The three actual template calls in the widened node worker: stage the
arithmetic context, construct the template, and clear its context copies.
The result consumes the raw stream and Taylor workspace while preserving
all reusable masters, including every port in the static-data bank. -/

namespace SubexponentialSAT.SubexpNodeTemplatePipeline

open BitProgram StructuredCalls
open SubexpSelectedConversions SubexpTemplateProgram
open SubexpNodeCacheSetup (copied)

abbrev Data := State 16 288
def ports : Fin 256 → Fin 288 := Fin.castAdd 32
theorem ports_injective : Function.Injective ports := Fin.castAdd_injective _ _
def localState (d : Data) := projectState id ports d

abbrev command : Cmd 16 288 :=
  .seq SubexpNodeWidePipeline.templateMetadata
    (.seq SubexpNodeWidePipeline.template SubexpNodeWidePipeline.clearTemplate)

def resultStacks (s : Fin 288 → List Bool) (output : List Bool) : Fin 288 → List Bool :=
  fun i => if h : i.val < 256 then
    SubexpNodeTemplateExecution.finishedStacks (s ∘ ports) output ⟨i.val,h⟩ else s i

theorem cleanupCost_prepared (d : SubexpNodeTemplateStage.Data) (ctx : Context)
    (raw : List Bool) (h : SubexpNodeTemplateReady.Ready d ctx raw) :
    SubexpNodeCacheSetup.cleanupCost (copied SubexpNodeStageCopies.templateMoves d) =
      SubexpNodeCacheSetup.cleanupCost d := by
  simp only [SubexpNodeCacheSetup.cleanupCost,
    SubexpNodeTemplateReady.copied_stacks d h.destinations]
  simp [SubexpNodeTemplateReady.preparedStacks]

theorem result_native (s : Fin 288 → List Bool) (output : List Bool) (i : Fin 256) :
    resultStacks s output (ports i) =
      SubexpNodeTemplateExecution.finishedStacks (s ∘ ports) output i := by
  unfold resultStacks
  split
  · rename_i h
    have hi : (⟨(ports i).val, h⟩ : Fin 256) = i := by
      apply Fin.ext
      simp only [ports, Fin.val_castAdd]
    rw [hi]
  · rename_i h
    exact (h (by simpa only [ports, Fin.val_castAdd] using i.isLt)).elim

theorem result_static (s : Fin 288 → List Bool) (output : List Bool)
    (i : Fin 288) (hi : 256 ≤ i.val) : resultStacks s output i = s i := by
  simp only [resultStacks, dite_eq_right (by omega : ¬ i.val < 256)]

variable {p D : ℕ} [Fact p.Prime]

theorem command_eval (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (hc : SubexpTemplateData.ContextGood ctx source target minusOne)
    (bs : List (SubexpTemplateData.Block p D)) (d : Data)
    (hr : SubexpNodeTemplateReady.Ready (localState d) ctx
      (SubexpTemplateProgram.encodeBlocks (bs.map SubexpTemplateData.rawBlock))) :
    ∃ n ≤ SubexpTemplateExecution.runCost ctx source target minusOne bs +
        SubexpNodeCacheSetup.cleanupCost (localState d) +
        9 * SubexpNodeTemplateReady.contextSize ctx + 75, ∃ out : Data,
      Eval command n d out ∧ out.stacks = resultStacks d.stacks
        (SubexpTemplateExecution.output ctx source target minusOne bs) := by
  let small := localState d
  let prep := copied SubexpNodeStageCopies.templateMoves small
  obtain ⟨hp,hready⟩ := SubexpNodeTemplateReady.prepare_eval small ctx _ hr
  let a := embedState id ports d prep
  have ep : Eval SubexpNodeWidePipeline.templateMetadata
      (SubexpNodeCacheSetup.copyCost SubexpNodeStageCopies.templateMoves small + 1) d a :=
    eval_liftCommand_from_state SubexpNodeStageCopies.prepareTemplate 128 204 id ports d
      Function.injective_id ports_injective hp
  have ha : projectState id ports a = prep :=
    projectState_embed id ports d prep Function.injective_id ports_injective
  obtain ⟨mid,⟨nt,hnt,ht⟩,hmid⟩ :=
    SubexpNodeTemplateExecution.program_runs ctx source target minusOne hc bs prep hready
  let b := embedState id ports a mid
  have et : Eval SubexpNodeWidePipeline.template nt a b := by
    apply eval_call_from_state SubexpNodeTemplateStage.program id ports a
      Function.injective_id ports_injective
    simpa only [ha] using ht
  have hb : projectState id ports b = mid :=
    projectState_embed id ports a mid Function.injective_id ports_injective
  obtain ⟨hclear,hfinal⟩ := SubexpNodeTemplateReady.clearTemplate_eval_exact
    small mid ctx _ (SubexpTemplateExecution.output ctx source target minusOne bs) hr hmid
  let final := SubexpNodeCacheSetup.cleared SubexpNodeStageCopies.templateWork mid
  let out := embedState id ports b final
  have ec : Eval SubexpNodeWidePipeline.clearTemplate
      (2 * SubexpNodeTemplateReady.contextSize ctx + 27 + 1) b out := by
    apply eval_liftCommand_from_state SubexpNodeStageCopies.clearTemplate 204 204 id ports b
      Function.injective_id ports_injective
    simpa only [hb] using hclear
  refine ⟨_,?_,out,ep.seq (et.seq ec),?_⟩
  · have hpc := SubexpNodeTemplateReady.prepare_cost small ctx _ hr
    have hcc := cleanupCost_prepared small ctx _ hr
    have hnt' : nt ≤ SubexpTemplateExecution.runCost ctx source target minusOne bs +
        SubexpNodeCacheSetup.cleanupCost (localState d) + 1 := by
      calc
        nt ≤ SubexpTemplateExecution.runCost ctx source target minusOne bs +
            SubexpNodeCacheSetup.cleanupCost prep + 1 := hnt
        _ = SubexpTemplateExecution.runCost ctx source target minusOne bs +
            SubexpNodeCacheSetup.cleanupCost (localState d) + 1 := by rw [hcc]
    rw [hpc]
    omega
  · funext i
    by_cases hi : i.val < 256
    · let j : Fin 256 := ⟨i.val,hi⟩
      have hj : ports j = i := Fin.ext rfl
      rw [← hj, result_native]
      exact (embedState_stack id ports b final ports_injective j).trans
        (congrFun hfinal j)
    · have hnot : ¬ ∃ j, ports j = i := by
        rintro ⟨j,hj⟩
        have hv := congrArg Fin.val hj
        change j.val = i.val at hv
        omega
      rw [result_static _ _ i (by omega)]
      exact (embedState_stack_frame id ports b final i hnot).trans
        ((embedState_stack_frame id ports a mid i hnot).trans
          (embedState_stack_frame id ports d prep i hnot))

end SubexponentialSAT.SubexpNodeTemplatePipeline

end OAI.Algorithms
