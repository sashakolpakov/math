import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainNodeArguments
import OAI.Algorithms.SubexponentialSAT.SubexpNodeWorkerMasterBound
import OAI.Algorithms.SubexponentialSAT.SubexpNodeUniformBound

namespace OAI.Algorithms

/-! Execute the installed node worker with the arguments produced by Main.
All storage/header, matrix-bank, and row-table premises of the generic
worker are discharged here. The local source relation is specialized by
the separate semantic provenance theorem. -/

namespace SubexponentialSAT.SubexpMainNodeExecution

noncomputable section

set_option quotPrecheck false

open BitProgram StructuredCalls SubexpMainProgram Subexp SubexpLayoutSpec
open SubexpLiftRing SubexpSelectedConversions SubexpSymbolicCost
open SubexpNodeWorkspace SubexpNodeStoreTransitions SubexpNodeContexts
open SubexpMomentSourceProgram SubexpMomentSourceSemantics
open SubexpLayoutPorts (Allocation)
open SubexpMainMomentData (store target)

variable {p k Δ r : ℕ} {τ : ℚ} {er es D : ℕ} [Fact p.Prime] [NeZero r]
  {alloc : Allocation es} {a middle layoutOut initialized : MainState er es}
  {hregs : 16 ≤ er} {hr : 0 < r} {hQ : 0 < p^4-1}
  {scopes : List (List ℕ)}
  {hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ}
  {tables : List (List Bool)}
  (c : Parameters p k Δ r τ) (h4 : c.h = 4)
  (h : SubexpMainLayoutExecution.Result hregs alloc a middle layoutOut
    p r Δ c.R D hr hQ scopes hd tables)
  (hi : SubexpMainNodeInitialization.Result alloc
    (SubexpMainNodeSetup.prepared alloc layoutOut) initialized D)
  (hP : (IncidencePlanSpec.pattern D scopes).Bounded k Δ)
  (hsize : c.Dstar ≤ D)
  (hthreshold : (Fintype.card (MulticolorTypes.UniversalType r (p^4-1) Δ) : ℚ)^3 *
    (1 + (Δ*k : ℕ)) ≤ τ^2*c.Dstar)
  (htail : SpectralRank.normalizedTail r (p^4-1-1)
    (TailInterval.intervalStart r (p^4-1) c.R) c.R ≤ τ/(Δ : ℚ))
  (i : Fin (p^4-1))

local notation "Masters" => store alloc initialized
local notation "Source" => SubexpMainNodeArguments.source h
local notation "Target" => target p D
local notation "MinusOne" => SubexpPreparedQuarticSetup.minusOne p (D+1)
local notation "HM" => SubexpMainMomentData.context_masters h hi
local notation "Theta" => SubexpMainNodeArguments.theta (D := D) i
local notation "Cache" => SubexpMainNodeArguments.cache h
local notation "Expr" => SubexpMainNodeArguments.rowExpr h
local notation "Rows" => SubexpDenseRowTableSemantics.expressionRows Expr D 0 scopes
local notation "Words" => SubexpMainMomentRouting.factorWords h
local notation "C" => SubexpMainLayoutEnumeration.context h i
local notation "Enum" => SubexpMainLayoutEnumeration.enumeration c h4 h hP hsize hthreshold htail i
local notation "Packing" => h.choices.packing.packing
local notation "Matrices" => SubexpMainLayoutEnumeration.images c h4 h i
local notation "Factor" => SubexpMainNodeArguments.factor h hi i
local notation "Order" => List.finRange scopes.length
local notation "Packet" => SubexpNodePacketRaw.packet Source Target Theta Factor
local notation "Bases" => List.ofFn (Enum).outerBase
local notation "Increments" => fun g => List.ofFn ((Enum).increment g)
local notation "Blocks" => RawTemplateRefinement.blocks Packing i Order Words Packet Bases Increments
local notation "BlocksGood" => RawTemplateRefinement.blocks_good Packing i Order Words Packet Bases Increments
local notation "TC" => templateContext Masters D
local notation "TemplateBytes" => SubexpTemplateExecution.output TC Source Target MinusOne Blocks
local notation "Ctx" => sourceContext Masters D TemplateBytes
local notation "Inputs" => SubexpNodeTemplateMoment.inputs Masters Source Target MinusOne HM Blocks BlocksGood
local notation "Coefficients" => QuarticSearch.liftedCoefficients p (D+1)
local notation "Ring" => LiftRing.Extension (QuarticSearch.poly Coefficients)
local notation "Node" => SubexpNodeIndexSemantics.thetaWord p D i
local notation "CacheBytes" => SubexpOriginCacheSemantics.taylorBytes p (D+1) Source
  (Target).modulus (Target).reduction Theta c.R (c.R+1) Rows

/-- A single input size shared by all nodes and all caller register states. -/
def inputSize (state : MainState er es) : ℕ :=
  SubexpNodeUniformBound.uniformSize p D c.R r (Rows).length (store alloc state)
    (SubexpNodeLiftData.liftedNodeWords p (D+1) (Source).modulus)
    (Source).modulus.bits (SubexpQuarticFlatNeg.flat (Target).zero)
    (SubexpQuarticFlatNeg.flat (Target).one) scopes tables
    ((Cache).map (List.map SubexpQuarticFlatNeg.flat))

local instance : One (QuarticCode p D) := ⟨(Target).one⟩
local instance : Zero (Raw p D) := ⟨[]⟩
local instance : One (Raw p D) := ⟨SubexpAlgorithm.rawOne D⟩

theorem program_runs
    (hvalid : ∀ scope ∈ scopes, ∀ v ∈ scope, v < D)
    (htables : tables.length = scopes.length)
    (hanswers : ∀ e : Fin scopes.length, (tables.getD e.val []).length = p^(scopes.get e).length)
    (hRw : CounterPrograms.value (a.stacks (persistent es 25)) = c.R)
    (reference : (Fin D → ℕ) → List (SubexpBlockAssemblySemantics.Block Ring (SymbolicCost.CoeffList D Ring)))
    (hprovenance :
      letI : One (QuarticCode p (Ctx).dimension) := ⟨(Target).one⟩
      ∀ z : Fin D → ℕ,
      letI : One (QuarticCode p ((Ctx).withExponent (SubexpExponentController.momentWord z)).dimension) := ⟨(Target).one⟩
      List.Forall₂
        (SubexpProducedSourceRefinement.BlockProvenance
          (ctx := (Ctx).withExponent (SubexpExponentController.momentWord z)) Coefficients z)
        ((Inputs).map (fun b => b.withExponent (SubexpExponentController.momentWord z))) (reference z))
    (d : State 16 288) (hactive : d.stacks = activeStacks Masters Node) :
    letI : One (QuarticCode p (Ctx).dimension) := ⟨(Target).one⟩
    ∃ (indexState basisState rawState templateState out : State 16 288) (n : ℕ)
      (sourceBytes : List Bool → List Bool)
      (actual : (Fin D → ℕ) → List (SubexpBlockAssemblySemantics.Block (QuarticCode p D) (Raw p D))),
      n ≤ SubexpNodeWorkerMasterBound.coefficient *
        (inputSize c h initialized)^3072 *
          2^(128*D) * ((Enum).iterationCount+1)^8 ∧
      Trace SubexpNodeConcretePipeline.worker n
        (d.withPC (some SubexpNodeConcretePipeline.worker.entry)) (out.withPC none) ∧
      out.stacks = finalStacks Masters
        (SubexpNodePhaseExecution.jet p D (Target).modulus (Target).reduction (Target).zero (Target).one
          (SubexpQueryOrder.visitSlots D) (SubexpNodeSourceJobs.expression p Ctx actual)
          (SubexpQueryOrder.generatedQueries D))
        (List.replicate (4 * baseWidth p (D+1)) false) ∧
      (∀ z : Fin D → ℕ,
        List.Forall₂ (SubexpSourceReference.BlockRel (coefficientValue p D Coefficients))
          (actual z) (reference z)) ∧
      (∀ z : Fin D → ℕ, sourceBytes (SubexpExponentController.momentWord z) =
        SubexpPostfixControl.serializeCode (SubexpDenseSerialization.encodeFixedQuarticCoefficients p D)
          (SubexpNodeSourceJobs.expression p Ctx actual z).compile) ∧
      (∀ z : Fin D → ℕ, (sourceBytes (SubexpExponentController.momentWord z)).length ≤
        uniformSourceBytes Ctx Inputs) ∧
      indexState.stacks = indexed Masters Node CacheBytes (List.replicate i.val true) ∧
      templateState.stacks = templated Masters (List.replicate i.val true) TemplateBytes ∧
      rawState.stacks = raw Masters Node CacheBytes (List.replicate i.val true)
        (SubexpTemplateProgram.encodeBlocks ((Blocks).map SubexpTemplateData.rawBlock)) ∧
      basisState.stacks = Function.update indexState.stacks 201
        (ProgramEncoding.encodeRecords ((Matrices).map SubexpNodeBankMap.payload)) := by
  let _ : One (QuarticCode p (Ctx).dimension) := ⟨(Target).one⟩
  let _ (bits : List Bool) : One (QuarticCode p ((Ctx).withExponent bits).dimension) :=
    ⟨(Target).one⟩
  obtain ⟨indexState,basisState,rawState,templateState,out,n,sourceBytes,actual,
    hn,htrace,hout,hrel,hbytes,hsourceSize,hindex,htemplated,hraw,hbasis⟩ :=
    SubexpNodeWorkerMasterBound.program_runs_original
      (c := SubexpMainLayoutSemantics.parameters c h4)
      (L := SubexpMainLayoutSemantics.layout c h4 h hP hsize hthreshold htail)
    C Enum hr hQ (SubexpMainLayoutEnumeration.context_split_le h i)
    (SubexpMainLayoutEnumeration.constraints c h4 h i)
    (SubexpMainLayoutEnumeration.context_good_normalized c h4 h i)
    (QuarticSearch.elements p) (QuarticSearch.mem_elements p) Packing
    Masters Source Target MinusOne HM Theta c.R Cache Expr scopes tables Words
    htables hanswers (SubexpMainNodeArguments.cache_large h)
    (SubexpMainLayoutEnumeration.arrays_eq c h4 h hP hsize hthreshold htail i)
    (SubexpMainMomentStatics.before h i) (SubexpMainMomentStatics.after h i)
    (SubexpMainMomentRouting.suffix h)
    (SubexpMainMomentStatics.basis_masters h hi i) (SubexpMainNodeArguments.packet_masters h hi)
    (SubexpMainLayoutEnumeration.context_metadata h i)
    (SubexpMainMomentRouting.assignment_prefix h hi Packet)
    (SubexpMainMomentRouting.word_width h hi) (SubexpMainMomentData.dimension h hi)
    (SubexpMainMomentData.index_word hi) (SubexpMainMomentRouting.metadata h hi)
    (SubexpMainMomentHeaders.radius h hi hRw) (SubexpMainNodeArguments.row_master h hi hvalid)
    (SubexpMainNodeArguments.node_master h hi) (SubexpMainMomentHeaders.moment_records hi)
    (SubexpMainMomentHeaders.raw_zero hi p) (SubexpMainMomentHeaders.raw_one h hi)
    (SubexpMainNodeArguments.target_zero_canonical (p := p) (D := D))
    (SubexpMainMomentHeaders.slots hi) (SubexpMainMomentHeaders.target_reduction h hi)
    reference hprovenance i rfl (SubexpMainNodeArguments.theta_word i) d hactive
  have hs : SubexpNodeWorkerMasterBound.inputSize
      (c := SubexpMainLayoutSemantics.parameters c h4)
      C Masters Source Target c.R Cache Expr scopes tables i ≤ inputSize c h initialized := by
    exact SubexpNodeUniformBound.originalSize_le_uniform p D c.R r (Rows).length
      Masters (SubexpNodeLiftData.liftedNodeWords p (D+1) (Source).modulus)
      (Source).modulus.bits (SubexpQuarticFlatNeg.flat (Target).zero)
      (SubexpQuarticFlatNeg.flat (Target).one) scopes tables
      ((Cache).map (List.map SubexpQuarticFlatNeg.flat)) i
  have hpower : (SubexpNodeWorkerMasterBound.inputSize
      (c := SubexpMainLayoutSemantics.parameters c h4)
      C Masters Source Target c.R Cache Expr scopes tables i)^3072 ≤
      (inputSize c h initialized)^3072 := by
    rw [show 3072 = 256 * 12 by norm_num, pow_mul, pow_mul]
    exact Nat.pow_le_pow_left (Nat.pow_le_pow_left hs 256) 12
  exact ⟨indexState,basisState,rawState,templateState,out,n,sourceBytes,actual,
    hn.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_left _ hpower))),
    htrace,hout,hrel,hbytes,hsourceSize,hindex,htemplated,hraw,hbasis⟩

end
end SubexponentialSAT.SubexpMainNodeExecution

end OAI.Algorithms
