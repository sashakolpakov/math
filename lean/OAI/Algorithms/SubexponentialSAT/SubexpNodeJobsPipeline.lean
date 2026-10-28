import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeSourceJobs
import OAI.Algorithms.SubexponentialSAT.SubexpNodeJobsReady
import OAI.Algorithms.SubexponentialSAT.SubexpNodeWidePipeline

namespace OAI.Algorithms

/-! The actual widened source/job stage, including physical context copies
and cleanup. Local packet provenance determines the generated expression
family; its bytes are obtained from the installed source constructor. -/

namespace SubexponentialSAT.SubexpNodeJobsPipeline

open BitProgram StructuredCalls
open SubexpMomentSourceProgram SubexpMomentSourceSemantics
open SubexpSymbolicCost SubexpQuarticRing SubexpLiftRing

abbrev Data := State 16 288
attribute [local simp] Fin.coe_ofNat_eq_mod
def ports : Fin 256 → Fin 288 := Fin.castAdd 32
theorem ports_injective : Function.Injective ports := Fin.castAdd_injective _ _
def localState (d : Data) := projectState id ports d

abbrev command : Cmd 16 288 :=
  .seq SubexpNodeWidePipeline.jobMetadata
    (.seq SubexpNodeWidePipeline.jobs SubexpNodeWidePipeline.clearJobs)

variable (p : ℕ) [Fact p.Prime] (ctx : Context)
  (htarget : ctx.target.length = baseWidth p (ctx.dimension+1))
  (hmodulus : BinaryArithmetic.toNat ctx.modulus = p^(ctx.dimension+1))
  (c : Fin 4 → ZMod (p^(ctx.dimension+1))) [One (QuarticCode p ctx.dimension)]

local notation "R" => LiftRing.Extension (QuarticSearch.poly c)
local notation "C" => QuarticCode p ctx.dimension
local notation "decode" => coefficientValue p ctx.dimension c

local instance : Zero (Raw p ctx.dimension) := ⟨[]⟩
local instance : One (Raw p ctx.dimension) := ⟨SubexpAlgorithm.rawOne ctx.dimension⟩
local instance (bits : List Bool) : One (QuarticCode p (ctx.withExponent bits).dimension) :=
  inferInstanceAs (One (QuarticCode p ctx.dimension))
local instance (bits : List Bool) : Zero (Raw p (ctx.withExponent bits).dimension) :=
  inferInstanceAs (Zero (Raw p ctx.dimension))
local instance (bits : List Bool) : One (Raw p (ctx.withExponent bits).dimension) :=
  inferInstanceAs (One (Raw p ctx.dimension))

include htarget hmodulus in
theorem command_eval
    (hzero : ctx.zero = SubexpDenseSerialization.encodeFixedQuarticCoefficients p ctx.dimension 0)
    (hone : ctx.one = SubexpDenseSerialization.encodeFixedQuarticCoefficients p ctx.dimension 1)
    (inputs : List (BlockData ctx))
    (hc : ContextGood
      (ctx.withExponent (SubexpExponentController.momentWord (fun _ : Fin ctx.dimension => 0)))
      (fun _ : Fin ctx.dimension => 0))
    (htemplate : ctx.template = encodeTemplate (inputs.map BlockData.template))
    (reference : (Fin ctx.dimension → ℕ) →
      List (SubexpBlockAssemblySemantics.Block R (SymbolicCost.CoeffList ctx.dimension R)))
    (hprovenance : ∀ a : Fin ctx.dimension → ℕ,
      List.Forall₂
        (SubexpProducedSourceRefinement.BlockProvenance
          (ctx := ctx.withExponent (SubexpExponentController.momentWord a)) c a)
        (inputs.map (fun b => b.withExponent (SubexpExponentController.momentWord a)))
        (reference a))
    (d : Data) (hr : SubexpNodeJobsReady.Ready (localState d) ctx)
    (h152 : d.stacks 152 = []) (h100 : d.stacks 100 = [])
    (h127 : d.stacks 127 = Encoding.encodeList id (SubexpOuterJobs.momentRecords ctx.dimension))
    (h248 : d.stacks 248 = []) (h249 : d.stacks 249 = []) :
    ∃ (sourceBytes : List Bool → List Bool)
      (actual : (Fin ctx.dimension → ℕ) →
        List (SubexpBlockAssemblySemantics.Block C (Raw p ctx.dimension)))
      (n : ℕ) (out : Data),
      n ≤ SubexpNodeJobsStage.masterBound sourceBytes ctx.dimension (indexBits ctx.dimension)
          (uniformTotalBudget ctx inputs + 8) (uniformSourceBytes ctx inputs) (localState d) +
        9 * SubexpNodeJobsReady.contextSize ctx + 2 * ctx.template.length + 69 ∧
      Eval command n d out ∧
      out.stacks = Function.update (Function.update d.stacks 200 []) 100
        (SubexpMomentProgram.input (SubexpQueryOrder.generatedJobs
          (SubexpDenseSerialization.encodeFixedQuarticCoefficients p ctx.dimension)
          (SubexpNodeSourceJobs.expression p ctx actual))) ∧
      (∀ a : Fin ctx.dimension → ℕ,
        List.Forall₂ (SubexpSourceReference.BlockRel decode) (actual a) (reference a)) ∧
      (∀ a : Fin ctx.dimension → ℕ,
        sourceBytes (SubexpExponentController.momentWord a) =
          SubexpPostfixControl.serializeCode
            (SubexpDenseSerialization.encodeFixedQuarticCoefficients p ctx.dimension)
            (SubexpNodeSourceJobs.expression p ctx actual a).compile) ∧
      ∀ a : Fin ctx.dimension → ℕ,
        (sourceBytes (SubexpExponentController.momentWord a)).length ≤ uniformSourceBytes ctx inputs := by
  let small := localState d
  let prep := SubexpNodeCacheSetup.copied SubexpNodeStageCopies.jobMoves small
  obtain ⟨hp,hsr,hgrid⟩ := SubexpNodeJobsReady.prepare_eval small ctx hr
  have hprep := SubexpNodeJobsReady.copied_stacks small hr.destinations
  have hprep_frame (i : Fin 256) (hi : i ∉ SubexpNodeJobsReady.copiedPorts) :
      prep.stacks i = small.stacks i :=
    (congrFun hprep i).trans (SubexpNodeJobsReady.prepared_frame small.stacks i hi)
  have h138 : prep.stacks 138 = [] := by
    have h := hr.work 0 (by decide)
    exact (hprep_frame 138 (by decide)).trans (by
      simpa [SubexpNodeJobsReady.sourcePort, SubexpNodeJobsStage.port,
        SubexpMomentSourceHost.ports] using h)
  have h139 : prep.stacks 139 = [] := by
    have h := hr.work 1 (by decide)
    exact (hprep_frame 139 (by decide)).trans (by
      simpa [SubexpNodeJobsReady.sourcePort, SubexpNodeJobsStage.port,
        SubexpMomentSourceHost.ports] using h)
  have h152' : prep.stacks 152 = [] := by
    exact (hprep_frame 152 (by decide)).trans (by
      simpa [small, localState, projectState, ports] using h152)
  have h100' : prep.stacks 100 = [] := by
    exact (hprep_frame 100 (by decide)).trans (by
      simpa [small, localState, projectState, ports] using h100)
  have h127' : prep.stacks 127 = Encoding.encodeList id (SubexpOuterJobs.momentRecords ctx.dimension) := by
    exact (hprep_frame 127 (by decide)).trans (by
      simpa [small, localState, projectState, ports] using h127)
  have h248' : prep.stacks 248 = [] := by
    exact (hprep_frame 248 (by decide)).trans (by
      simpa [small, localState, projectState, ports] using h248)
  have h249' : prep.stacks 249 = [] := by
    exact (hprep_frame 249 (by decide)).trans (by
      simpa [small, localState, projectState, ports] using h249)
  obtain ⟨sourceBytes,actual,mid,⟨nj,hnj,hj⟩,hmid,hrel,hbytes,hsize⟩ :=
    SubexpNodeSourceJobs.typed_program_runs p ctx htarget hmodulus c hzero hone inputs hc htemplate
      reference hprovenance prep hsr hgrid h138 h139 h152' h100' h127' h248' h249'
  let a := embedState id ports d prep
  have ep : Eval SubexpNodeWidePipeline.jobMetadata
      (SubexpNodeCacheSetup.copyCost SubexpNodeStageCopies.jobMoves small + 1) d a :=
    eval_liftCommand_from_state SubexpNodeStageCopies.prepareJobs 109 140 id ports d
      Function.injective_id ports_injective hp
  have ha : projectState id ports a = prep :=
    projectState_embed id ports d prep Function.injective_id ports_injective
  let b := embedState id ports a mid
  have ej : Eval SubexpNodeWidePipeline.jobs nj a b := by
    apply eval_call_from_state SubexpNodeSourceJobs.program id ports a
      Function.injective_id ports_injective
    simpa only [ha] using hj
  have hb : projectState id ports b = mid :=
    projectState_embed id ports a mid Function.injective_id ports_injective
  obtain ⟨hc',hfinal⟩ := SubexpNodeJobsReady.clearJobs_eval_exact small mid ctx _ hr hmid
  let final := SubexpNodeCacheSetup.cleared SubexpNodeStageCopies.jobWork mid
  let out := embedState id ports b final
  have ec : Eval SubexpNodeWidePipeline.clearJobs
      (2 * (SubexpNodeJobsReady.contextSize ctx + ctx.template.length) + 27 + 1) b out := by
    apply eval_liftCommand_from_state SubexpNodeStageCopies.clearJobs 200 200 id ports b
      Function.injective_id ports_injective
    simpa only [hb] using hc'
  refine ⟨sourceBytes,actual,_,out,?_,ep.seq (ej.seq ec),?_,hrel,hbytes,hsize⟩
  · have hpc := SubexpNodeJobsReady.prepare_cost small ctx hr
    have hbnd : SubexpNodeJobsStage.masterBound sourceBytes ctx.dimension (indexBits ctx.dimension)
        (uniformTotalBudget ctx inputs + 8) (uniformSourceBytes ctx inputs) prep =
        SubexpNodeJobsStage.masterBound sourceBytes ctx.dimension (indexBits ctx.dimension)
        (uniformTotalBudget ctx inputs + 8) (uniformSourceBytes ctx inputs) small := by
      simp only [SubexpNodeJobsStage.masterBound,prep,hprep]
      simp [SubexpNodeJobsReady.preparedStacks]
    have hnj' : nj ≤ SubexpNodeJobsStage.masterBound sourceBytes ctx.dimension
        (indexBits ctx.dimension) (uniformTotalBudget ctx inputs + 8)
        (uniformSourceBytes ctx inputs) (localState d) := by
      calc
        nj ≤ SubexpNodeJobsStage.masterBound sourceBytes ctx.dimension
            (indexBits ctx.dimension) (uniformTotalBudget ctx inputs + 8)
            (uniformSourceBytes ctx inputs) prep := hnj
        _ = SubexpNodeJobsStage.masterBound sourceBytes ctx.dimension
            (indexBits ctx.dimension) (uniformTotalBudget ctx inputs + 8)
            (uniformSourceBytes ctx inputs) (localState d) := hbnd
    rw [hpc]
    omega
  · funext i
    by_cases hi : i.val < 256
    · let j : Fin 256 := ⟨i.val,hi⟩
      have hj : ports j = i := Fin.ext rfl
      rw [← hj]
      have h100j : ports j = 100 ↔ j = 100 := by
        change ports j = ports 100 ↔ j = 100
        exact ports_injective.eq_iff
      have h200j : ports j = 200 ↔ j = 200 := by
        change ports j = ports 200 ↔ j = 200
        exact ports_injective.eq_iff
      have hout := (embedState_stack id ports b final ports_injective j).trans (congrFun hfinal j)
      simpa only [out, SubexpNodeJobsReady.finishedStacks, Function.update_apply,
        h100j, h200j, small, localState, projectState, Function.comp_apply] using hout
    · have hnot : ¬ ∃ j, ports j = i := by
        rintro ⟨j,hj⟩
        have hv := congrArg Fin.val hj
        change j.val = i.val at hv
        omega
      have h100i : i ≠ 100 := by intro h; subst i; norm_num at hi
      have h200i : i ≠ 200 := by intro h; subst i; norm_num at hi
      rw [Function.update_of_ne h100i,Function.update_of_ne h200i]
      exact (embedState_stack_frame id ports b final i hnot).trans
        ((embedState_stack_frame id ports a mid i hnot).trans
          (embedState_stack_frame id ports d prep i hnot))

end SubexponentialSAT.SubexpNodeJobsPipeline

end OAI.Algorithms
