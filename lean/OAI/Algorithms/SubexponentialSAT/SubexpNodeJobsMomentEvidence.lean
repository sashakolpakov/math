import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeJobsMoment

namespace OAI.Algorithms

/-! The same actual source/job/moment execution also retains the exact
serialized-expression equality needed by its quantitative bound. -/

namespace SubexponentialSAT.SubexpNodeJobsMoment

open BitProgram StructuredCalls
open SubexpMomentSourceProgram SubexpMomentSourceSemantics
open SubexpSymbolicCost SubexpQuarticRing SubexpLiftRing SubexpCanonicalWords

variable (p : ℕ) [Fact p.Prime] (ctx : Context)
  (htarget : ctx.target.length = baseWidth p (ctx.dimension+1))
  (hmodulus : BinaryArithmetic.toNat ctx.modulus = p^(ctx.dimension+1))
  (c : Fin 4 → ZMod (p^(ctx.dimension+1))) [One (QuarticCode p ctx.dimension)]

local notation "D" => ctx.dimension
local notation "C" => QuarticCode p D
local notation "R" => LiftRing.Extension (QuarticSearch.poly c)
local notation "decode" => coefficientValue p D c
local notation "slots" => SubexpQueryOrder.visitSlots D
local notation "queries" => SubexpQueryOrder.generatedQueries D

local instance : Zero (Raw p D) := ⟨[]⟩
local instance : One (Raw p D) := ⟨SubexpAlgorithm.rawOne D⟩
local instance (bits : List Bool) : One (QuarticCode p (ctx.withExponent bits).dimension) :=
  inferInstanceAs (One C)
local instance (bits : List Bool) : Zero (Raw p (ctx.withExponent bits).dimension) :=
  inferInstanceAs (Zero (Raw p D))
local instance (bits : List Bool) : One (Raw p (ctx.withExponent bits).dimension) :=
  inferInstanceAs (One (Raw p D))

include htarget hmodulus in
theorem command_eval_with_bytes
    (hzero : ctx.zero = SubexpDenseSerialization.encodeFixedQuarticCoefficients p D 0)
    (hone : ctx.one = SubexpDenseSerialization.encodeFixedQuarticCoefficients p D 1)
    (inputs : List (BlockData ctx))
    (hc : ContextGood
      (ctx.withExponent (SubexpExponentController.momentWord (fun _ : Fin D => 0)))
      (fun _ : Fin D => 0))
    (htemplate : ctx.template = encodeTemplate (inputs.map BlockData.template))
    (reference : (Fin D → ℕ) → List (SubexpBlockAssemblySemantics.Block R (SymbolicCost.CoeffList D R)))
    (hprovenance : ∀ a : Fin D → ℕ,
      List.Forall₂
        (SubexpProducedSourceRefinement.BlockProvenance
          (ctx := ctx.withExponent (SubexpExponentController.momentWord a)) c a)
        (inputs.map (fun b => b.withExponent (SubexpExponentController.momentWord a))) (reference a))
    (M : SubexpPreparedQuartic.Modulus p (D+1)) (reduction zero : C)
    (hz : quotientDenote c (zero.map (wordValue p (D+1))) = 0)
    (hcanonical : CanonicalQuad p (D+1) zero)
    (width : List Bool) (hwidth : width.length = baseWidth p (D+1))
    (d : Data) (hr : SubexpNodeJobsReady.Ready (SubexpNodeJobsPipeline.localState d) ctx)
    (hphase : SubexpMomentStep.Ready (phaseState d) M.bits width)
    (hcontext : SubexpDenseMultiplication.ContextReady
      (SubexpEvaluationProgram.contextOf (phaseState d).stacks) M.bits width
      (SubexpDenseProgram.Projection.queryBytes slots) (SubexpQuarticFlatMul.flat reduction)
      (List.replicate (indexBits D) true))
    (h152 : d.stacks 152 = []) (h100 : d.stacks 100 = [])
    (h127 : d.stacks 127 = Encoding.encodeList id (SubexpOuterJobs.momentRecords D))
    (h248 : d.stacks 248 = []) (h249 : d.stacks 249 = [])
    (h101 : d.stacks 101 = []) (h102 : d.stacks 102 = []) (h104 : d.stacks 104 = [])
    (h106 : d.stacks 106 = []) (h107 : d.stacks 107 = []) (h108 : d.stacks 108 = []) :
    ∃ (sourceBytes : List Bool → List Bool)
      (actual : (Fin D → ℕ) → List (SubexpBlockAssemblySemantics.Block C (Raw p D)))
      (n : ℕ) (out : Data),
      n ≤ SubexpNodeJobsStage.masterBound sourceBytes D (indexBits D)
          (uniformTotalBudget ctx inputs + 8) (uniformSourceBytes ctx inputs)
          (SubexpNodeJobsPipeline.localState d) +
        9 * SubexpNodeJobsReady.contextSize ctx + 2 * ctx.template.length + 69 +
        SubexpConcreteMomentPhase.cost p D M reduction zero 1 slots
          (SubexpNodeSourceJobs.expression p ctx actual) queries +
        SubexpNodePhaseExecution.clearCost (SubexpNodeWidePhase.localState d) + 2 ∧
      Eval command n d out ∧
      out.stacks = SubexpNodeWidePhase.resultStacks (Function.update d.stacks 200 [])
        (SubexpNodePhaseExecution.jet p D M reduction zero 1 slots
          (SubexpNodeSourceJobs.expression p ctx actual) queries)
        (List.replicate (4 * baseWidth p (D+1)) false) ∧
      (∀ a : Fin D → ℕ,
        List.Forall₂ (SubexpSourceReference.BlockRel decode) (actual a) (reference a)) ∧
      (∀ a : Fin D → ℕ,
        sourceBytes (SubexpExponentController.momentWord a) =
          SubexpPostfixControl.serializeCode
            (SubexpDenseSerialization.encodeFixedQuarticCoefficients p D)
            (SubexpNodeSourceJobs.expression p ctx actual a).compile) ∧
      ∀ a : Fin D → ℕ,
        (sourceBytes (SubexpExponentController.momentWord a)).length ≤ uniformSourceBytes ctx inputs := by
  obtain ⟨sourceBytes,actual,nj,mid,hnj,hj,hs,hrel,hbytes,hsize⟩ :=
    SubexpNodeJobsPipeline.command_eval p ctx htarget hmodulus c hzero hone inputs hc htemplate
      reference hprovenance d hr h152 h100 h127 h248 h249
  let expr := SubexpNodeSourceJobs.expression p ctx actual
  have hslots : ∀ a ∈ slots, SymbolicCost.Retained D a :=
    fun a ha => (SubexpQueryOrder.mem_visitSlots D a).mp ha
  have hmD : mid.stacks 109 = List.replicate D true := by
    simpa [hs,SubexpNodeJobsPipeline.localState,projectState,SubexpNodeJobsPipeline.ports] using hr.dimension
  have hstream : mid.stacks 100 = Encoding.encodeList id (SubexpMomentPhase.records p D expr queries) := by
    rw [SubexpMomentPhase.records_generated]
    simpa [SubexpMomentProgram.input,SubexpBlueprintRows.encodeList_map,expr] using congrFun hs 100
  have h101' : mid.stacks 101 = [] := by simpa [hs] using h101
  have h102' : mid.stacks 102 = [] := by simpa [hs] using h102
  have h104' : mid.stacks 104 = [] := by simpa [hs] using h104
  have h106' : mid.stacks 106 = [] := by simpa [hs] using h106
  have h107' : mid.stacks 107 = [] := by simpa [hs] using h107
  have h108' : mid.stacks 108 = [] := by simpa [hs] using h108
  obtain ⟨np,hnp,out,hp,hout⟩ :=
    SubexpNodeWidePhase.command_eval p D M reduction zero 1 slots expr c hz hcanonical width hwidth
      hslots mid queries (SubexpMomentPhase.generatedQueries_valid D)
      (ready_jobs d mid _ _ _ hs hphase) (context_jobs d mid _ _ _ _ _ _ hs hcontext)
      hmD hstream h101' h102' h104' h106' h107' h108'
  refine ⟨sourceBytes,actual,nj+np,out,?_,hj.seq hp,?_,hrel,hbytes,hsize⟩
  · have hclear : SubexpNodePhaseExecution.clearCost (SubexpNodeWidePhase.localState mid) =
        SubexpNodePhaseExecution.clearCost (SubexpNodeWidePhase.localState d) := by
      simp [SubexpNodePhaseExecution.clearCost,SubexpNodeWidePhase.localState,projectState,
        SubexpNodeWidePhase.ports,hs]
    have hnp' : np ≤ SubexpConcreteMomentPhase.cost p D M reduction zero 1 slots
        (SubexpNodeSourceJobs.expression p ctx actual) queries +
        SubexpNodePhaseExecution.clearCost (SubexpNodeWidePhase.localState d) + 2 := by
      calc
        np ≤ SubexpConcreteMomentPhase.cost p D M reduction zero 1 slots expr queries +
            SubexpNodePhaseExecution.clearCost (SubexpNodeWidePhase.localState mid) + 2 := hnp
        _ = _ := by rw [hclear]
    omega
  · rw [hout,hs]
    funext i
    by_cases h100i : i = 100 <;>
      simp [SubexpNodeWidePhase.resultStacks,Function.update_apply,h100i,expr]

end SubexponentialSAT.SubexpNodeJobsMoment

end OAI.Algorithms
