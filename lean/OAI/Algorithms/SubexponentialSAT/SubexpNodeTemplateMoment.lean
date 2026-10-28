import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodePreparedMoment
import OAI.Algorithms.SubexponentialSAT.SubexpNodeTemplatePipeline
import OAI.Algorithms.SubexponentialSAT.SubexpTemplateSourceData

namespace OAI.Algorithms

/-! The actual raw-template to moment suffix. The source constructor's
typed inputs are obtained from the blocks consumed by the physical template
program, and the exact generated-template identity is derived internally. -/

namespace SubexponentialSAT.SubexpNodeTemplateMoment

open BitProgram StructuredCalls SubexpNodeWorkspace SubexpNodeStoreTransitions
open SubexpNodeContexts SubexpSelectedConversions SubexpLiftRing SubexpQuarticRing
open SubexpMomentSourceProgram SubexpMomentSourceSemantics SubexpSymbolicCost

abbrev Data := State 16 288
abbrev command : Cmd 16 288 :=
  .seq SubexpNodeTemplatePipeline.command SubexpNodeJobsMoment.command

variable {p D : ℕ} [Fact p.Prime] [One (QuarticCode p D)]
  (masters : Store) (source : Prepared p 0) (target : Prepared p D)
  (minusOne : SubexpQuarticRing.Word (baseWidth p (D+1)))
  (hm : SubexpNodeContextSemantics.Masters masters source target minusOne)
  (bs : List (SubexpTemplateData.Block p D))
  (hbs : ∀ b ∈ bs, SubexpTemplateSourceData.BlockGood b)

local notation "TC" => templateContext masters D
local notation "templateBytes" => SubexpTemplateExecution.output TC source target minusOne bs
local notation "Ctx" => sourceContext masters D templateBytes
local notation "C" => QuarticCode p D
local notation "coefficients" => QuarticSearch.liftedCoefficients p (D+1)
local notation "R" => LiftRing.Extension (QuarticSearch.poly coefficients)
local notation "slots" => SubexpQueryOrder.visitSlots D
local notation "queries" => SubexpQueryOrder.generatedQueries D

def inputs : List (BlockData Ctx) :=
  SubexpTemplateSourceData.blocksData Ctx hm.sourceWidth TC source target minusOne bs hbs

local instance : Zero (Raw p D) := ⟨[]⟩
local instance : One (Raw p D) := ⟨SubexpAlgorithm.rawOne D⟩
local instance : One (QuarticCode p (Ctx).dimension) := inferInstanceAs (One C)
local instance : Zero (Raw p (Ctx).dimension) := inferInstanceAs (Zero (Raw p D))
local instance : One (Raw p (Ctx).dimension) := inferInstanceAs (One (Raw p D))
local instance (bits : List Bool) : One (QuarticCode p ((Ctx).withExponent bits).dimension) :=
  inferInstanceAs (One C)

theorem command_eval
    (hzero : masters 122 = SubexpDenseSerialization.encodeFixedQuarticCoefficients p D 0)
    (hone : masters 123 = SubexpDenseSerialization.encodeFixedQuarticCoefficients p D 1)
    (reference : (Fin D → ℕ) → List (SubexpBlockAssemblySemantics.Block R (SymbolicCost.CoeffList D R)))
    (hprovenance : ∀ a : Fin D → ℕ,
      List.Forall₂
        (SubexpProducedSourceRefinement.BlockProvenance
          (ctx := (Ctx).withExponent (SubexpExponentController.momentWord a)) coefficients a)
        ((inputs masters source target minusOne hm bs hbs).map
          (fun b => b.withExponent (SubexpExponentController.momentWord a))) (reference a))
    (hcanonical : SubexpCanonicalWords.CanonicalQuad p (D+1) target.zero)
    (hD : masters 109 = List.replicate D true)
    (hI : masters 92 = List.replicate (indexBits D) true)
    (hslots : masters 25 = SubexpDenseProgram.Projection.queryBytes slots)
    (hreduction : masters 91 = SubexpQuarticFlatMul.flat target.reduction)
    (h127 : masters 127 = Encoding.encodeList id (SubexpOuterJobs.momentRecords D))
    (node cache index : List Bool) (d : Data)
    (hs : d.stacks = raw masters node cache index
      (SubexpTemplateProgram.encodeBlocks (bs.map SubexpTemplateData.rawBlock))) :
    ∃ (mid : Data) (nt : ℕ),
      nt ≤ SubexpTemplateExecution.runCost TC source target minusOne bs +
        SubexpNodeCacheSetup.cleanupCost (SubexpNodeTemplatePipeline.localState d) +
        9 * SubexpNodeTemplateReady.contextSize TC + 75 ∧
      mid.stacks = templated masters index templateBytes ∧
      ∃ (sourceBytes : List Bool → List Bool)
        (actual : (Fin D → ℕ) → List (SubexpBlockAssemblySemantics.Block C (Raw p D)))
        (nj : ℕ) (out : Data),
        nj ≤ SubexpNodeJobsStage.masterBound sourceBytes D (indexBits D)
          (uniformTotalBudget Ctx (inputs masters source target minusOne hm bs hbs) + 8)
          (uniformSourceBytes Ctx (inputs masters source target minusOne hm bs hbs))
          (SubexpNodeJobsPipeline.localState mid) +
          9 * SubexpNodeJobsReady.contextSize Ctx + 2 * (templateBytes).length + 69 +
          SubexpConcreteMomentPhase.cost p D target.modulus target.reduction target.zero 1 slots
            (SubexpNodeSourceJobs.expression p Ctx actual) queries +
          SubexpNodePhaseExecution.clearCost (SubexpNodeWidePhase.localState mid) + 2 ∧
        Eval command (nt+nj) d out ∧
        out.stacks = finalStacks masters
          (SubexpNodePhaseExecution.jet p D target.modulus target.reduction target.zero 1 slots
            (SubexpNodeSourceJobs.expression p Ctx actual) queries)
          (List.replicate (4 * baseWidth p (D+1)) false) ∧
        (∀ a : Fin D → ℕ,
          List.Forall₂ (SubexpSourceReference.BlockRel (coefficientValue p D coefficients))
            (actual a) (reference a)) ∧
        (∀ a : Fin D → ℕ, sourceBytes (SubexpExponentController.momentWord a) =
          SubexpPostfixControl.serializeCode
            (SubexpDenseSerialization.encodeFixedQuarticCoefficients p D)
            (SubexpNodeSourceJobs.expression p Ctx actual a).compile) ∧
        ∀ a : Fin D → ℕ, (sourceBytes (SubexpExponentController.momentWord a)).length ≤
          uniformSourceBytes Ctx (inputs masters source target minusOne hm bs hbs) := by
  have hlocal : (SubexpNodeTemplatePipeline.localState d).stacks =
      raw masters node cache index (SubexpTemplateProgram.encodeBlocks
        (bs.map SubexpTemplateData.rawBlock)) ∘ Fin.castAdd 32 := by
    funext i
    exact congrFun hs (Fin.castAdd 32 i)
  have ready := SubexpNodeContexts.template_ready masters D node cache index _ hD hI
    (SubexpNodeTemplatePipeline.localState d) hlocal
  obtain ⟨nt,hnt,mid,ht,hmid⟩ := SubexpNodeTemplatePipeline.command_eval TC source target
    minusOne (SubexpNodeContextSemantics.template_good masters source target minusOne hm) bs d ready
  have hmids : mid.stacks = templated masters index templateBytes := by
    rw [hmid,hs,template_result]
  have hbytes : templateBytes = encodeTemplate
      ((inputs masters source target minusOne hm bs hbs).map BlockData.template) :=
    (SubexpTemplateSourceData.blocksData_template_bytes Ctx hm.sourceWidth TC
      source target minusOne bs hbs).symm
  obtain ⟨bytes,actual,nj,out,hnj,hj,hout,hrel,hsource,hsize⟩ :=
    SubexpNodePreparedMoment.command_eval masters source target minusOne hm templateBytes
      hzero hone (inputs masters source target minusOne hm bs hbs) hbytes reference hprovenance
      hcanonical hD hI hslots hreduction h127 index mid hmids
  exact ⟨mid,nt,hnt,hmids,bytes,actual,nj,out,hnj,ht.seq hj,hout,hrel,hsource,hsize⟩

end SubexponentialSAT.SubexpNodeTemplateMoment

end OAI.Algorithms
