import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeWorkerExecution
import OAI.Algorithms.SubexponentialSAT.SubexpNodeBlueprintEvidence

namespace OAI.Algorithms

/-! Full concrete worker execution with the retained basis frame for its
bank-stage copy-cost substitution. All previous interfaces are unchanged. -/

namespace SubexponentialSAT.SubexpNodeWorkerExecution

open BitProgram StructuredCalls SubexpLiftRing SubexpSelectedConversions
open SubexpNodeWorkspace SubexpNodeStoreTransitions SubexpNodeContexts
open MulticolorTypes Subexp.ConstructivePacking Subexp.BlockSearch
open Subexp.GlobalBasisRefinement (pairs packingLocation)
open SubexpMomentSourceProgram SubexpMomentSourceSemantics SubexpSymbolicCost

variable {p r Q Δ D : ℕ} [Fact p.Prime] [codeOne : One (QuarticCode p D)]
  (C : Subexp.GlobalBasisInput.Context p r Q Δ) (hr : 0 < r) (hQ : 0 < Q)
  (hsplit : ∀ g, (C.tables g).split ≤ (C.tables g).dimension)
  {m : Fin r → ℕ}
  (constraint : ∀ g, Fin (m g) → Fin (C.tables g).dimension → ZMod p)
  (good : ∀ g, GoodPair (constraint g) (pairs C hsplit g))
  (alphabet : List (ZMod p)) (complete : ∀ x, x ∈ alphabet)
  (P : PackingData (Fin D) (UniversalType r Q Δ))
  (masters : Store) (source : Prepared p 0) (target : Prepared p D)
  (minusOne : SubexpQuarticRing.Word (baseWidth p (D+1)))
  (hm : SubexpNodeContextSemantics.Masters masters source target minusOne)
  (theta : SubexpTaylorRow.Code p (D+1)) (R : ℕ)
  (cache : List (List (SubexpFactorPacketProvenance.Code p D)))
  (expr : ℕ → ℕ → ℕ → SubexpTaylorRowCorrectness.RowExpr p)
  (scopes : List (List ℕ)) (tables : List (List Bool))
  (words : Fin scopes.length → MulticolorTypes.Word r Q)
  (bases : List (Fin D → ZMod p)) (increments : Fin r → List (Fin D → ZMod p))

local notation "rows" => SubexpDenseRowTableSemantics.expressionRows expr D 0 scopes
local notation "cacheBytes" => SubexpOriginCacheSemantics.taylorBytes p (D+1) source
  target.modulus target.reduction theta R (R+1) rows
local notation "factor" => SubexpNodePacketInputs.factor source target theta R (masters 129)
  hm.sourceWidth cache target.zero target.one expr scopes tables
local notation "order" => List.finRange scopes.length
local notation "items" => SubexpNodePacketRaw.items source target theta order factor words
local notation "matrices" => Subexp.GlobalBasisMatrixBytes.images C hr hQ hsplit
  constraint good alphabet complete P
local notation "blocks" => Subexp.RawTemplateRefinement.blocks P C.position order words
  (SubexpNodePacketRaw.packet source target theta factor) bases increments
local notation "blocksGood" => Subexp.RawTemplateRefinement.blocks_good P C.position order words
  (SubexpNodePacketRaw.packet source target theta factor) bases increments
local notation "TC" => templateContext masters D
local notation "templateBytes" => SubexpTemplateExecution.output TC source target minusOne blocks
local notation "Ctx" => sourceContext masters D templateBytes
local notation "inputs" => SubexpNodeTemplateMoment.inputs masters source target minusOne hm blocks blocksGood
local notation "coefficients" => QuarticSearch.liftedCoefficients p (D+1)
local notation "Ring" => LiftRing.Extension (QuarticSearch.poly coefficients)
local notation "slots" => SubexpQueryOrder.visitSlots D
local notation "queries" => SubexpQueryOrder.generatedQueries D

local instance : Zero (Raw p D) := ⟨[]⟩
local instance : One (Raw p D) := ⟨SubexpAlgorithm.rawOne D⟩
local instance : One (QuarticCode p (Ctx).dimension) := codeOne
local instance (bits : List Bool) : One (QuarticCode p ((Ctx).withExponent bits).dimension) :=
  codeOne

theorem program_runs_with_basis
    (htables : tables.length = scopes.length)
    (hanswers : ∀ e : Fin scopes.length, (tables.getD e.val []).length = p^(scopes.get e).length)
    (hcache : p ≤ cache.length)
    (hbank : ProgramEncoding.encodeRecords ((matrices).map SubexpNodeBankMap.bankList) =
      SubexpRawTemplate.bankBundle (bases.map Subexp.RawTemplateRefinement.vectorBytes)
        (List.ofFn fun g => (increments g).map Subexp.RawTemplateRefinement.vectorBytes))
    (before : List (List Bool)) (tail suffix : List Bool)
    (H : SubexpNodeBasisWorkspace.Masters C P.blockCount P.leftovers.length D before tail masters)
    (T : SubexpNodeBlueprintWorkspace.PacketMasters masters scopes tables
      (cache.map (List.map SubexpQuarticFlatNeg.flat))
      (SubexpQuarticFlatNeg.flat target.zero) (SubexpQuarticFlatNeg.flat target.one))
    (hmeta : C.metadata = Subexp.PackingMetadata.records P
      (fun v => Subexp.PackingMetadata.unary v.val) Subexp.CollisionProgram.encodeType)
    (hassignment : masters 258 = SubexpFactorRoutingTraversal.words items ++ suffix)
    (hwordwidth : (masters 260).length = Q*r)
    (hD : masters 109 = List.replicate D true)
    (hI : masters 92 = List.replicate (indexBits D) true)
    (hmetadata : masters 269 = Subexp.SupportSelectionProgram.metadataTable P)
    (h126 : masters 126 = List.replicate (R+1) true)
    (h255 : masters 255 = SubexpTaylorCacheControl.encodeRows SubexpTaylorRow.flat
      (SubexpNodeCacheTyped.rows p (D+1) source R rows))
    (h125 : masters 125 = ProgramEncoding.encodeRecords
      (SubexpNodeLiftData.liftedNodeWords p (D+1) source.modulus))
    (h127 : masters 127 = Encoding.encodeList id (SubexpOuterJobs.momentRecords D))
    (hzero : masters 122 = SubexpDenseSerialization.encodeFixedQuarticCoefficients p D 0)
    (hone : masters 123 = SubexpDenseSerialization.encodeFixedQuarticCoefficients p D 1)
    (hcanonical : SubexpCanonicalWords.CanonicalQuad p (D+1) target.zero)
    (hslots : masters 25 = SubexpDenseProgram.Projection.queryBytes slots)
    (hreduction : masters 91 = SubexpQuarticFlatMul.flat target.reduction)
    (reference : (Fin D → ℕ) → List (SubexpBlockAssemblySemantics.Block Ring (SymbolicCost.CoeffList D Ring)))
    (hprovenance :
      letI : One (QuarticCode p (Ctx).dimension) := codeOne
      ∀ a : Fin D → ℕ,
      letI : One (QuarticCode p ((Ctx).withExponent (SubexpExponentController.momentWord a)).dimension) := codeOne
      List.Forall₂
        (SubexpProducedSourceRefinement.BlockProvenance
          (ctx := (Ctx).withExponent (SubexpExponentController.momentWord a)) coefficients a)
        ((inputs).map (fun b => b.withExponent (SubexpExponentController.momentWord a))) (reference a))
    (i : Fin (p^4-1)) (hposition : C.position.val = i.val)
    (htheta : SubexpNodeIndexSemantics.thetaWord p D i = SubexpTaylorRow.flat theta)
    (d : Data) (hactive : d.stacks = activeStacks masters (SubexpNodeIndexSemantics.thetaWord p D i)) :
    letI : One (QuarticCode p (Ctx).dimension) := codeOne
    ∃ (cachedState indexState basisState originState packetState rawState templateState out : Data)
      (nc ni nb nt ns : ℕ) (sourceBytes : List Bool → List Bool)
      (actual : (Fin D → ℕ) → List (SubexpBlockAssemblySemantics.Block (QuarticCode p D) (Raw p D))),
      nc ≤ SubexpNodeCacheSetup.prepareCost (SubexpNodeCacheIndex.localState d) +
        SubexpTaylorCacheMap.tableBudget (rows).length D (R+1) (R+1) (baseWidth p (D+1)) + 1 ∧
      ni ≤ SubexpNodeIndexProgram.budget (SubexpNodeIndexSemantics.thetaWord p D i)
        (SubexpNodeLiftData.liftedNodeWords p (D+1) source.modulus) + 1 ∧
      nb ≤ SubexpNodeBasisExecution.runtimeBound C P.blockCount P.leftovers.length
          (List.ofFn (packingLocation P)) indexState +
        (SubexpNodeBankStage.budget basisState matrices + 1) +
        SubexpOriginMap.tableBound (rows).length D (baseWidth p (D+1))
          (baseWidth p 1) source.modulus.bits.length R +
        SubexpFactorPacketProgram.runtimeBound
          (SubexpFactorPacketCorrectness.physicalInputs source target theta cache source.modulus.bits
            target.zero target.one ((order).map factor)) +
        (SubexpRawTemplate.commandCost P C.position items suffix
          (bases.map Subexp.RawTemplateRefinement.vectorBytes)
          (List.ofFn fun g => (increments g).map Subexp.RawTemplateRefinement.vectorBytes)
          packetState.stacks + 1) + 1 ∧
      nt ≤ SubexpTemplateExecution.runCost TC source target minusOne blocks +
        SubexpNodeCacheSetup.cleanupCost (SubexpNodeTemplatePipeline.localState rawState) +
        9 * SubexpNodeTemplateReady.contextSize TC + 75 ∧
      ns ≤ SubexpNodeJobsStage.masterBound sourceBytes D (indexBits D)
          (uniformTotalBudget Ctx inputs + 8) (uniformSourceBytes Ctx inputs)
          (SubexpNodeJobsPipeline.localState templateState) +
        9 * SubexpNodeJobsReady.contextSize Ctx + 2 * (templateBytes).length + 69 +
        SubexpConcreteMomentPhase.cost p D target.modulus target.reduction target.zero 1 slots
          (SubexpNodeSourceJobs.expression p Ctx actual) queries +
        SubexpNodePhaseExecution.clearCost (SubexpNodeWidePhase.localState templateState) + 2 ∧
      Trace SubexpNodeConcretePipeline.worker (nc + (ni + (nb + (nt+ns))) + 1)
        (d.withPC (some SubexpNodeConcretePipeline.worker.entry)) (out.withPC none) ∧
      out.stacks = finalStacks masters
        (SubexpNodePhaseExecution.jet p D target.modulus target.reduction target.zero 1 slots
          (SubexpNodeSourceJobs.expression p Ctx actual) queries)
        (List.replicate (4 * baseWidth p (D+1)) false) ∧
      (∀ a : Fin D → ℕ,
        List.Forall₂ (SubexpSourceReference.BlockRel (coefficientValue p D coefficients))
          (actual a) (reference a)) ∧
      (∀ a : Fin D → ℕ, sourceBytes (SubexpExponentController.momentWord a) =
        SubexpPostfixControl.serializeCode (SubexpDenseSerialization.encodeFixedQuarticCoefficients p D)
          (SubexpNodeSourceJobs.expression p Ctx actual a).compile) ∧
      (∀ a : Fin D → ℕ, (sourceBytes (SubexpExponentController.momentWord a)).length ≤
        uniformSourceBytes Ctx inputs) ∧
      cachedState.stacks = cached masters (SubexpNodeIndexSemantics.thetaWord p D i) cacheBytes ∧
      indexState.stacks = indexed masters (SubexpNodeIndexSemantics.thetaWord p D i)
        cacheBytes (List.replicate C.position.val true) ∧
      templateState.stacks = templated masters (List.replicate C.position.val true) templateBytes ∧
      originState.stacks = SubexpNodeBasisBankOrigin.finishedStacks indexState.stacks
        (ProgramEncoding.encodeRecords ((matrices).map SubexpNodeBankMap.bankList))
        (SubexpNodeOriginExecution.output p (D+1) source target.modulus target.reduction theta
          R (R+1) (Nat.succ_pos R) source.modulus (masters 129) hm.sourceWidth rows) ∧
      packetState.stacks = Function.update (Function.update originState.stacks 227 []) 225
        (Encoding.encodeList id ((items).map Prod.snd)) ∧
      rawState.stacks = raw masters (SubexpNodeIndexSemantics.thetaWord p D i) cacheBytes
        (List.replicate C.position.val true)
        (SubexpTemplateProgram.encodeBlocks ((blocks).map SubexpTemplateData.rawBlock)) ∧
      basisState.stacks = Function.update indexState.stacks 201
        (ProgramEncoding.encodeRecords ((matrices).map SubexpNodeBankMap.payload)) := by
  let : One (QuarticCode p (Ctx).dimension) := codeOne
  let (bits : List Bool) : One (QuarticCode p ((Ctx).withExponent bits).dimension) := codeOne
  obtain ⟨nc,hnc,cachedState,hc,hcs⟩ := SubexpNodeCacheIndex.cache_step p (D+1) source
    target.modulus (Nat.succ_pos D) target.reduction theta (masters 10) hm.targetWidth R (R+1) D rows
    (SubexpNodeBlueprintExecution.row_width expr D 0 scopes) masters _ d hactive htheta
    hm.targetModulus rfl hreduction h126 h255
  obtain ⟨ni,hni,indexState,hi,his⟩ := SubexpNodeCacheIndex.index_step p D source.modulus i
    masters cacheBytes cachedState hcs h125
  have hindex : indexState.stacks = indexed masters (SubexpNodeIndexSemantics.thetaWord p D i)
      cacheBytes (List.replicate C.position.val true) := by simpa only [hposition] using his
  obtain ⟨basisState,originState,packetState,rawState,nb,hnb,hb,horigin,hpack,hraw,hbasis⟩ :=
    SubexpNodeBlueprintExecution.program_runs_with_basis C hr hQ hsplit constraint good alphabet complete P
      source target theta R (masters 129) hm.sourceWidth cache expr scopes tables words
      htables hanswers hcache bases increments hbank before tail suffix _ masters indexState hindex H
      ⟨hm.sourceModulus,rfl,rfl⟩ hm.targetWidth T hmeta hassignment H.colors hwordwidth hD hmetadata
  obtain ⟨templateState,nt,hnt,hts,sourceBytes,actual,ns,out,hns,hs,hout,hrel,hbytes,hsize⟩ :=
    SubexpNodeTemplateMoment.command_eval masters source target minusOne hm blocks blocksGood
      hzero hone reference hprovenance hcanonical hD hI hslots hreduction h127 _ cacheBytes
      (List.replicate C.position.val true) rawState hraw
  exact ⟨cachedState,indexState,basisState,originState,packetState,rawState,templateState,out,
    nc,ni,nb,nt,ns,sourceBytes,actual,hnc,hni,hnb,hnt,hns,grouped_trace hc hi hb hs,
    hout,hrel,hbytes,hsize,hcs,hindex,hts,horigin,hpack,hraw,hbasis⟩

end SubexponentialSAT.SubexpNodeWorkerExecution

end OAI.Algorithms
