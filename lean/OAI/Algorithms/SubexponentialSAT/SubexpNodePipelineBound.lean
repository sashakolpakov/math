import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeCostAssembly
import OAI.Algorithms.SubexponentialSAT.Subexp.NodePreludeSum

namespace OAI.Algorithms

/-! Complete numerical budget of the actual node pipeline. Each component
is bounded from its actual producer; no execution-cost or output-size
certificate is a premise of this theorem. The separate worker execution
proof supplies precisely these component costs and byte identities. -/

namespace SubexponentialSAT.SubexpNodePipelineBound

open Subexp.ConstructivePacking SubexpLiftRing SubexpSelectedConversions
open SubexpNodeTemplateIterationBound SubexpNodeOriginalInputBound
open SubexpNodeWorkerBound SubexpNodeWorkerIterationBound SubexpNodePreludeBound
open SubexpQuarticRing SubexpSymbolicCost SymbolicCost

variable {p D k Δ r : ℕ} {τ : ℚ} [Fact p.Prime]
variable {F E : Type*} [Fintype F] [Field E] [Algebra (ZMod p) E]
variable {P : Factor.Pattern (Fin D) F} {c : SubexpLayoutSpec.Parameters p k Δ r τ}
variable {L : SubexpLayoutSpec.Layout (E := E) P c} {node : Fin c.Q}
variable (source : Prepared p 0) (target : SubexpPreparedQuartic.Modulus p (D+1))
variable (cacheReduction cacheTheta : SubexpTaylorRow.Code p (D+1))
variable (R N : ℕ) (hN : 0 < N) (width : List Bool) (hw : width.length = baseWidth p 1)
variable (es : List (List (SubexpTaylorRowCorrectness.RowExpr p)))
variable (scopes : List (List ℕ)) (tables : List (List Bool))
variable (cache : List (List (List Bool))) (zero one : List Bool)
variable (C : ℕ) (hC : ∀ row ∈ es, row.length ≤ C)

local notation "PacketInput" => SubexpNodePacketReady.inputs p (D+1) source target
  cacheReduction cacheTheta R N hN width hw es scopes tables cache zero one
local notation "PacketStatic" => SubexpNodePacketInputBound.staticSize p (D+1) R N C es.length
  source.modulus.bits zero one scopes tables cache

include hC in
theorem pipelineCost_le (e : SubexpLayoutSpec.EnumerationData L node)
    (heq : (PacketInput).origins.length = (PacketInput).columns.length)
    (hincidence : ((PacketInput).scopes.map List.length).sum = (PacketInput).origins.length)
    (hm : 0 < BinaryArithmetic.toNat (PacketInput).modulus)
    (hcache : BinaryArithmetic.toNat (PacketInput).modulus ≤ (PacketInput).cache.length)
    (packing : PackingData (Fin D) (MulticolorTypes.UniversalType r c.Q Δ))
    (items : List (SubexpFactorRoutingTraversal.Item r c.Q)) (suffix old226 : List Bool)
    (store : SubexpRawTemplate.Store) (q : ℕ)
    (hpackets : Encoding.encodeList id (items.map Prod.snd) = SubexpFactorPacketProgram.output PacketInput)
    (h226 : store 226 = old226) (h227 : store 227 = [])
    (preparation : SubexpBlueprintFactor.Context) (preparedTarget : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (baseWidth p (D + 1)))
    (hc : SubexpTemplateData.ContextGood preparation source preparedTarget minusOne)
    (bs : List (SubexpTemplateData.Block p D))
    (hq : SubexpTemplateCostBounds.TaylorBound q bs)
    (hraw : SubexpTemplateProgram.encodeBlocks (bs.map SubexpTemplateData.rawBlock) =
      SubexpRawTemplate.outputBytes packing node items
        (SubexpNodeBankBounds.outerBanks e) (SubexpNodeBankBounds.innerBanks e))
    (ctx : SubexpMomentSourceProgram.Context) (d : SubexpNodeWorkerBound.Data)
    (cleanup : SubexpNodeCacheSetup.Data)
    (hprepared : ctx.template = SubexpTemplateExecution.output preparation source preparedTarget minusOne bs)
    (M : SubexpPreparedQuartic.Modulus p (ctx.dimension + 1))
    (reduction z o : QuarticCode p ctx.dimension) (slots : List (RawIndex ctx.dimension))
    (inputs : List (SubexpMomentSourceProgram.BlockData ctx)) (bytes : List Bool → List Bool)
    (expr : (Fin ctx.dimension → ℕ) → Algorithm.Expr (CoeffList ctx.dimension (QuarticCode p ctx.dimension)))
    (htemplate : ctx.template = SubexpMomentSourceProgram.encodeTemplate
      (inputs.map SubexpMomentSourceProgram.BlockData.template))
    (hmaster : d.stacks 127 = Encoding.encodeList id (SubexpOuterJobs.momentRecords ctx.dimension))
    (hs : ∀ a ∈ slots, Retained ctx.dimension a) (hslots : slots.length ≤ slotCount ctx.dimension)
    (hbytes : ∀ a : Fin ctx.dimension → ℕ, bytes (SubexpExponentController.momentWord a) =
      SubexpPostfixControl.serializeCode
        (SubexpDenseSerialization.encodeFixedQuarticCoefficients p ctx.dimension) (expr a).compile)
    (hsize : ∀ a : Fin ctx.dimension → ℕ, (bytes (SubexpExponentController.momentWord a)).length ≤
      SubexpMomentSourceProgram.uniformSourceBytes ctx inputs)
    (matrices : List (SubexpNodeBankMap.Matrix p D))
    (harrays : matrices.map (fun A => Subexp.MatrixImageEnumeration.bankRecords p A.entries) =
      SubexpNodeBankBounds.outerBanks e :: SubexpNodeBankBounds.innerBanks e)
    (mPre CPre RPre NPre BPre bPre modulusPre : ℕ)
    (cacheState : SubexpNodeCacheSetup.Data) (query : List Bool) (nodes : List (List Bool))
    (basisContext : Subexp.GlobalBasisInput.Context p r c.Q Δ) (count leftovers : ℕ)
    (locations : List (Subexp.GlobalBasisInput.Location r c.Q Δ))
    (before : List (List Bool)) (basisTail : List Bool)
    (basisState bankState : StructuredProgram.State 16 288)
    (hBasis : SubexpNodeBasisExecution.Input basisContext count leftovers locations.length
      before basisTail basisState)
    (hLocations : basisContext.locations 0 locations) :
    Subexp.NodePreludeSum.cost mPre CPre RPre NPre BPre bPre modulusPre cacheState query nodes
        basisContext count leftovers locations basisState bankState matrices +
      SubexpFactorPacketProgram.runtimeBound PacketInput +
      ((SubexpRawTemplate.commandCost packing node items suffix
      (SubexpNodeBankBounds.outerBanks e) (SubexpNodeBankBounds.innerBanks e) store + 1) +
      SubexpTemplateExecution.runCost preparation source preparedTarget minusOne bs +
      SubexpNodeCacheSetup.cleanupCost cleanup + 9 * SubexpNodeTemplateReady.contextSize preparation + 75 +
      jobsPhaseCost p ctx M reduction z o slots inputs bytes expr d) + 1 ≤
      7 * coefficient * (SubexpNodeCostAssembly.scale
        (Subexp.NodePreludeSum.scale p D mPre CPre RPre NPre BPre bPre modulusPre
          cacheState query nodes basisState bankState) PacketStatic
        (SubexpNodeTemplateSuffixBound.scale (p := p) PacketStatic packing items suffix old226 q ctx d cleanup preparation))^768 *
        2^(128 * ctx.dimension) * (e.iterationCount + 1)^8 := by
  have hp := Subexp.NodePreludeSum.cost_le e matrices harrays mPre CPre RPre NPre BPre bPre
    modulusPre cacheState query nodes basisContext count leftovers locations before basisTail
    basisState bankState hBasis hLocations
  have hk := SubexpNodeCostAssembly.packetRuntime_le p (D+1) source target cacheReduction cacheTheta
    R N hN width hw es scopes tables cache zero one C hC heq hincidence hm hcache
  have hsuffix := SubexpNodeTemplateSuffixBound.cost_le source target cacheReduction cacheTheta
    R N hN width hw es scopes tables cache zero one C hC e heq hincidence hm hcache packing items
    suffix old226 store q hpackets h226 h227 preparation preparedTarget minusOne hc bs hq hraw
    ctx d cleanup hprepared M reduction z o slots inputs bytes expr htemplate hmaster hs hslots hbytes hsize
  exact SubexpNodeCostAssembly.sum_bounds _ _ _ _ _ _ _ _ (by omega) hp hk hsuffix

end SubexponentialSAT.SubexpNodePipelineBound

end OAI.Algorithms
