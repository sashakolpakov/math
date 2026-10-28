import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeContextSemantics
import OAI.Algorithms.SubexponentialSAT.SubexpNodePhaseReady
import OAI.Algorithms.SubexponentialSAT.SubexpNodeJobsMomentEvidence

namespace OAI.Algorithms

/-! A generated, typed template is consumed by the real source/job/moment
suffix. Every machine-workspace premise is derived from the canonical
template boundary and physically stored masters. -/

namespace SubexponentialSAT.SubexpNodePreparedMoment

open BitProgram StructuredCalls SubexpNodeWorkspace SubexpNodeStoreTransitions
open SubexpNodeContexts SubexpSelectedConversions SubexpLiftRing SubexpQuarticRing
open SubexpMomentSourceProgram SubexpMomentSourceSemantics SubexpSymbolicCost

abbrev Data := State 16 288

theorem cleared_template (masters : Store) (index template : List Bool) :
    Function.update (templated masters index template) 200 [] = jobs masters index [] := by
  let base := Function.update (initialStacks masters) 116 index
  have h200 : Function.update base 200 [] = base := Function.update_eq_self 200 base
  have h100 : Function.update base 100 [] = base := Function.update_eq_self 100 base
  change Function.update (Function.update base 200 template) 200 [] = Function.update base 100 []
  rw [Function.update_idem,h200,h100]

variable {p D : ℕ} [Fact p.Prime]
  (masters : Store) (source : Prepared p 0) (target : Prepared p D)
  (minusOne : Word (baseWidth p (D+1)))
  (hm : SubexpNodeContextSemantics.Masters masters source target minusOne)
  (template : List Bool)

local notation "Ctx" => sourceContext masters D template
local notation "C" => QuarticCode p D
local notation "coefficients" => QuarticSearch.liftedCoefficients p (D+1)
local notation "R" => LiftRing.Extension (QuarticSearch.poly coefficients)
local notation "slots" => SubexpQueryOrder.visitSlots D
local notation "queries" => SubexpQueryOrder.generatedQueries D

variable [One (QuarticCode p D)]
local instance : Zero (Raw p D) := ⟨[]⟩
local instance : One (Raw p D) := ⟨SubexpAlgorithm.rawOne D⟩
local instance : One (QuarticCode p (Ctx).dimension) := inferInstanceAs (One C)
local instance : Zero (Raw p (Ctx).dimension) := inferInstanceAs (Zero (Raw p D))
local instance : One (Raw p (Ctx).dimension) := inferInstanceAs (One (Raw p D))
local instance (bits : List Bool) : One (QuarticCode p ((Ctx).withExponent bits).dimension) :=
  inferInstanceAs (One C)

include hm in
theorem command_eval
    (hzero : masters 122 = SubexpDenseSerialization.encodeFixedQuarticCoefficients p D 0)
    (hone : masters 123 = SubexpDenseSerialization.encodeFixedQuarticCoefficients p D 1)
    (inputs : List (BlockData Ctx))
    (htemplate : template = encodeTemplate (inputs.map BlockData.template))
    (reference : (Fin D → ℕ) → List (SubexpBlockAssemblySemantics.Block R (SymbolicCost.CoeffList D R)))
    (hprovenance : ∀ a : Fin D → ℕ,
      List.Forall₂
        (SubexpProducedSourceRefinement.BlockProvenance
          (ctx := (Ctx).withExponent (SubexpExponentController.momentWord a)) coefficients a)
        (inputs.map (fun b => b.withExponent (SubexpExponentController.momentWord a))) (reference a))
    (hcanonical : SubexpCanonicalWords.CanonicalQuad p (D+1) target.zero)
    (hD : masters 109 = List.replicate D true)
    (hI : masters 92 = List.replicate (indexBits D) true)
    (hslots : masters 25 = SubexpDenseProgram.Projection.queryBytes slots)
    (hreduction : masters 91 = SubexpQuarticFlatMul.flat target.reduction)
    (h127 : masters 127 = Encoding.encodeList id (SubexpOuterJobs.momentRecords D))
    (index : List Bool) (d : Data)
    (hs : d.stacks = templated masters index template) :
    ∃ (sourceBytes : List Bool → List Bool)
      (actual : (Fin D → ℕ) → List (SubexpBlockAssemblySemantics.Block C (Raw p D)))
      (n : ℕ) (out : Data),
      n ≤ SubexpNodeJobsStage.masterBound sourceBytes D (indexBits D)
          (uniformTotalBudget Ctx inputs + 8) (uniformSourceBytes Ctx inputs)
          (SubexpNodeJobsPipeline.localState d) +
        9 * SubexpNodeJobsReady.contextSize Ctx + 2 * template.length + 69 +
        SubexpConcreteMomentPhase.cost p D target.modulus target.reduction target.zero (1 : C) slots
          (SubexpNodeSourceJobs.expression p Ctx actual) queries +
        SubexpNodePhaseExecution.clearCost (SubexpNodeWidePhase.localState d) + 2 ∧
      Eval SubexpNodeJobsMoment.command n d out ∧
      out.stacks = finalStacks masters
        (SubexpNodePhaseExecution.jet p D target.modulus target.reduction target.zero (1 : C) slots
          (SubexpNodeSourceJobs.expression p Ctx actual) queries)
        (List.replicate (4 * baseWidth p (D+1)) false) ∧
      (∀ a : Fin D → ℕ,
        List.Forall₂ (SubexpSourceReference.BlockRel (coefficientValue p D coefficients))
          (actual a) (reference a)) ∧
      (∀ a : Fin D → ℕ,
        sourceBytes (SubexpExponentController.momentWord a) =
          SubexpPostfixControl.serializeCode
            (SubexpDenseSerialization.encodeFixedQuarticCoefficients p D)
            (SubexpNodeSourceJobs.expression p Ctx actual a).compile) ∧
      ∀ a : Fin D → ℕ,
        (sourceBytes (SubexpExponentController.momentWord a)).length ≤ uniformSourceBytes Ctx inputs := by
  have hlocal : (SubexpNodeJobsPipeline.localState d).stacks =
      templated masters index template ∘ Fin.castAdd 32 := by
    funext i
    exact congrFun hs (Fin.castAdd 32 i)
  have ready := SubexpNodeContexts.jobs_ready masters D index template hD hI
    (SubexpNodeJobsPipeline.localState d) hlocal
  have hp := SubexpNodePhaseReady.templated_ready masters d index template
    target.modulus.bits (masters 10) (SubexpDenseProgram.Projection.queryBytes slots)
    (SubexpQuarticFlatMul.flat target.reduction) (List.replicate (indexBits D) true)
    hs hm.targetModulus rfl hslots hreduction hI
  have empty (i : Fin 288) (hi : i ∈ SubexpNodePhaseReady.initPorts) :=
    SubexpNodePhaseReady.templated_init masters d index template hs i hi
  have h152 : d.stacks 152 = [] := by rw [hs]; rfl
  have h248 : d.stacks 248 = [] := by rw [hs]; rfl
  have h249 : d.stacks 249 = [] := by rw [hs]; rfl
  have master127 : d.stacks 127 = Encoding.encodeList id (SubexpOuterJobs.momentRecords D) := by
    rw [hs]
    exact h127
  have hmodulus : BinaryArithmetic.toNat (Ctx).modulus = p^(D+1) := by
    change BinaryArithmetic.toNat (masters 5) = _
    rw [hm.targetModulus,target.modulus.value]
  obtain ⟨bytes,actual,n,out,hn,he,hout,hrel,hbytes,hsize⟩ :=
    SubexpNodeJobsMoment.command_eval_with_bytes p Ctx hm.targetWidth hmodulus coefficients
      hzero hone inputs (SubexpNodeContextSemantics.source_good masters source target minusOne hm
        template (fun _ => 0)) htemplate reference hprovenance
      target.modulus target.reduction target.zero target.zero_spec hcanonical
      (masters 10) hm.targetWidth d ready hp.1 hp.2 h152 (empty 100 (by decide)) master127
      h248 h249 (empty 101 (by decide)) (empty 102 (by decide)) (empty 104 (by decide))
      (empty 106 (by decide)) (empty 107 (by decide)) (empty 108 (by decide))
  refine ⟨bytes,actual,n,out,hn,he,?_,hrel,hbytes,hsize⟩
  rw [hout,hs,cleared_template,phase_result]
  rfl

end SubexponentialSAT.SubexpNodePreparedMoment

end OAI.Algorithms
