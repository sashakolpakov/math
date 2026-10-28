import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodePacketInputBound
import OAI.Algorithms.SubexponentialSAT.SubexpNodeWorkerIterationBound

namespace OAI.Algorithms

/-! Replace every generated packet/template/source size in the worker
suffix by original master bytes, numeric parameters, and the proved
enumeration count. -/

namespace SubexponentialSAT.SubexpNodeOriginalInputBound

open Subexp.ConstructivePacking SubexpLiftRing SubexpSelectedConversions
open SubexpNodeTemplateIterationBound SubexpNodePacketBoundaryBound
open SubexpNodeWorkerBound SubexpNodeWorkerIterationBound
open SubexpQuarticRing SubexpSymbolicCost SymbolicCost

def originalScale {p D r Q Δ : ℕ} (packetStaticSize : ℕ)
    (packing : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (items : List (SubexpFactorRoutingTraversal.Item r Q)) (suffix old226 : List Bool)
    (q : ℕ) (ctx : SubexpMomentSourceProgram.Context) (d : SubexpNodeWorkerBound.Data) : ℕ :=
  packetStaticSize + (SubexpFactorRoutingTraversal.words items ++ suffix).length +
  (Subexp.SupportSelectionProgram.metadataTable packing).length + old226.length +
  D + Q + r + Subexp.MatrixWordEncoding.width p +
  SubexpTemplateCostBounds.scale p D q + suffixSize p ctx d + 1

private theorem original_arithmetic (B A S : ℕ) (_hS : 1 ≤ S) (hAS : A ≤ S)
    (hB : B ≤ 79 * A^4 + S) : B ≤ 80 * S^4 := by
  have ha := Nat.mul_le_mul_left 79 (Nat.pow_le_pow_left hAS 4)
  have hs : S ≤ S^4 := Nat.le_self_pow (by decide) S
  omega

private theorem scale_arithmetic (B S T : ℕ) (hS : 1 ≤ S)
    (hB : B ≤ 301 * (80 * S^4)^4) (hT : T ≤ S) :
    B + T ≤ 20000000000 * S^16 := by
  have hb : B ≤ 12328960000 * S^16 := by
    convert hB using 1
    ring
  have hs : S ≤ S^16 := Nat.le_self_pow (by decide) S
  omega

variable {p D r Q Δ : ℕ} [Fact p.Prime]
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
theorem scale_le_static
    (heq : (PacketInput).origins.length = (PacketInput).columns.length)
    (hincidence : ((PacketInput).scopes.map List.length).sum = (PacketInput).origins.length)
    (hm : 0 < BinaryArithmetic.toNat (PacketInput).modulus)
    (hcache : BinaryArithmetic.toNat (PacketInput).modulus ≤ (PacketInput).cache.length)
    (packing : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (items : List (SubexpFactorRoutingTraversal.Item r Q)) (suffix old226 : List Bool)
    (store : SubexpRawTemplate.Store) (q : ℕ)
    (ctx : SubexpMomentSourceProgram.Context) (d : SubexpNodeWorkerBound.Data)
    (hpackets : Encoding.encodeList id (items.map Prod.snd) = SubexpFactorPacketProgram.output PacketInput)
    (h226 : store 226 = old226) (h227 : store 227 = []) :
    SubexpNodeWorkerIterationBound.scale (p := p) packing items suffix store q ctx d ≤
      20000000000 * (originalScale (p := p) PacketStatic packing items suffix old226 q ctx d)^16 := by
  let S := originalScale (p := p) PacketStatic packing items suffix old226 q ctx d
  have hS : 1 ≤ S := by dsimp [S, originalScale]; omega
  have hPS : PacketStatic ≤ S := by dsimp [S, originalScale]; omega
  have hi := SubexpNodePacketInputBound.inputSize_le p (D+1) source target cacheReduction cacheTheta
    R N hN width hw es scopes tables cache zero one C hC
  have hOS : originalSize (p := p) PacketInput packing items suffix old226 ≤ 80 * S^4 := by
    apply original_arithmetic _ PacketStatic S hS hPS
    unfold originalSize
    dsimp [S, originalScale]
    omega
  have hb := (SubexpNodePacketBoundaryBound.boundarySize_le PacketInput heq hincidence hm hcache
    packing items suffix old226 store hpackets h226 h227).trans
    (Nat.mul_le_mul_left 301 (Nat.pow_le_pow_left hOS 4))
  have hrest : SubexpTemplateCostBounds.scale p D q + suffixSize p ctx d ≤ S := by
    dsimp [S, originalScale]
    omega
  change boundarySize (p := p) packing items suffix store +
    SubexpTemplateCostBounds.scale p D q + suffixSize p ctx d ≤ _
  have h := scale_arithmetic _ S _ hS hb hrest
  simpa only [Nat.add_assoc] using h

def coefficient : ℕ := 10^78 * 20000000000^48

private theorem cost_arithmetic (A S J X cost : ℕ)
    (hA : A ≤ 20000000000 * S^16)
    (hc : cost ≤ 10^78 * A^48 * X^5 * J^8) :
    cost ≤ coefficient * S^768 * X^5 * J^8 := by
  apply hc.trans
  calc
    _ ≤ 10^78 * (20000000000 * S^16)^48 * X^5 * J^8 := by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hA 48)))
    _ = _ := by unfold coefficient; ring

section ActualLayout

variable {k : ℕ} {τ : ℚ} {F E : Type*} [Fintype F] [Field E] [Algebra (ZMod p) E]
variable {P : Factor.Pattern (Fin D) F} {c : SubexpLayoutSpec.Parameters p k Δ r τ}
variable {L : SubexpLayoutSpec.Layout (E := E) P c} {node : Fin c.Q}

include hC in
/-- Full source/job/moment suffix, with all generated-size bounds replaced
by the actual prior producers. Remaining premises are structural/byte
identities supplied by the concrete pipeline and its source witness. -/
theorem jobsPhaseCost_le_original (e : SubexpLayoutSpec.EnumerationData L node)
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
      SubexpMomentSourceProgram.uniformSourceBytes ctx inputs) :
    jobsPhaseCost p ctx M reduction z o slots inputs bytes expr d ≤
      coefficient * (originalScale (p := p) PacketStatic packing items suffix old226 q ctx d)^768 *
        2^(128 * ctx.dimension) * (e.iterationCount + 1)^8 := by
  have hscale := scale_le_static source target cacheReduction cacheTheta R N hN width hw es
    scopes tables cache zero one C hC heq hincidence hm hcache packing items suffix old226
    store q ctx d hpackets h226 h227
  have hcost := SubexpNodeWorkerIterationBound.jobsPhaseCost_le_iterations e packing items suffix store q
    preparation source preparedTarget minusOne hc bs hq hraw ctx d hprepared M reduction z o slots
    inputs bytes expr htemplate hmaster hs hslots hbytes hsize
  apply (cost_arithmetic _ _ _ _ _ hscale hcost).trans
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (monomial_fifth_le ctx.dimension))

end ActualLayout

end SubexponentialSAT.SubexpNodeOriginalInputBound

end OAI.Algorithms
