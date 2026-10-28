import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeCanonicalCostInputs

namespace OAI.Algorithms

/-! One explicit bound for raw-template assembly, template preparation,
metadata/cleanup, current-moment source generation, jobs and evaluation. -/

namespace SubexponentialSAT.SubexpNodeTemplateSuffixBound

open Subexp.ConstructivePacking SubexpLiftRing SubexpSelectedConversions
open SubexpNodeTemplateIterationBound SubexpNodeOriginalInputBound
open SubexpNodeWorkerBound SubexpNodeWorkerIterationBound SubexpNodePreludeBound
open SubexpQuarticRing SubexpSymbolicCost SymbolicCost

def envelope (S J X : ℕ) : ℕ := coefficient * S^768 * X * J^8

private theorem promote (S J X a u v : ℕ) (hS : 1 ≤ S) (hJ : 1 ≤ J) (hX : 1 ≤ X)
    (ha : a ≤ coefficient) (hu : u ≤ 768) (hv : v ≤ 8) :
    a * S^u * J^v ≤ envelope S J X := by
  unfold envelope
  calc
    _ ≤ coefficient * S^768 * J^8 := Nat.mul_le_mul
      (Nat.mul_le_mul ha (Nat.pow_le_pow_right hS hu)) (Nat.pow_le_pow_right hJ hv)
    _ = coefficient * S^768 * 1 * J^8 := by ring
    _ ≤ coefficient * S^768 * X * J^8 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hX)

private theorem raw_coefficient :
    167042000000 * 20000000000^8 ≤ coefficient := by
  unfold coefficient
  exact Nat.mul_le_mul (by norm_num)
    (Nat.pow_le_pow_right (by norm_num) (by decide))

private theorem preparation_coefficient : 10^27 * 20000000000^13 ≤ coefficient := by
  unfold coefficient
  exact Nat.mul_le_mul (by norm_num)
    (Nat.pow_le_pow_right (by norm_num) (by decide))

private theorem small_coefficient : 128 ≤ coefficient := by
  have h : 1 ≤ (20000000000 : ℕ)^48 := Nat.one_le_pow _ _ (by norm_num)
  have hm := Nat.mul_le_mul_left (10^78) h
  unfold coefficient
  norm_num at hm ⊢

def scale {p D r Q Δ : ℕ} (packetStatic : ℕ)
    (packing : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (items : List (SubexpFactorRoutingTraversal.Item r Q)) (suffix old226 : List Bool)
    (q : ℕ) (ctx : SubexpMomentSourceProgram.Context) (d : SubexpNodeWorkerBound.Data)
    (cleanup : SubexpNodeCacheSetup.Data) (preparation : SubexpBlueprintFactor.Context) : ℕ :=
  originalScale (p := p) packetStatic packing items suffix old226 q ctx d +
    cleanupInputSize cleanup + SubexpNodeTemplateReady.contextSize preparation + 1

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
theorem cost_le (e : SubexpLayoutSpec.EnumerationData L node)
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
      SubexpMomentSourceProgram.uniformSourceBytes ctx inputs) :
    (SubexpRawTemplate.commandCost packing node items suffix
      (SubexpNodeBankBounds.outerBanks e) (SubexpNodeBankBounds.innerBanks e) store + 1) +
      SubexpTemplateExecution.runCost preparation source preparedTarget minusOne bs +
      SubexpNodeCacheSetup.cleanupCost cleanup + 9 * SubexpNodeTemplateReady.contextSize preparation + 75 +
      jobsPhaseCost p ctx M reduction z o slots inputs bytes expr d ≤
      4 * coefficient * (scale (p := p) PacketStatic packing items suffix old226 q ctx d cleanup preparation)^768 *
        2^(128 * ctx.dimension) * (e.iterationCount + 1)^8 := by
  let S := scale (p := p) PacketStatic packing items suffix old226 q ctx d cleanup preparation
  let J := e.iterationCount + 1
  let X := 2^(128 * ctx.dimension)
  have hS : 1 ≤ S := by dsimp [S, scale]; omega
  have hJ : 1 ≤ J := by dsimp [J]; omega
  have hX : 1 ≤ X := Nat.one_le_pow _ _ (by decide)
  have hOS : originalScale (p := p) PacketStatic packing items suffix old226 q ctx d ≤ S := by
    dsimp [S, scale]
    omega
  have hscale := scale_le_static source target cacheReduction cacheTheta R N hN width hw es
    scopes tables cache zero one C hC heq hincidence hm hcache packing items suffix old226
    store q ctx d hpackets h226 h227
  have hfull : SubexpNodeWorkerIterationBound.scale (p := p) packing items suffix store q ctx d ≤
      20000000000 * S^16 := hscale.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hOS 16))
  have hb : boundarySize (p := p) packing items suffix store ≤ 20000000000 * S^16 := by
    apply le_trans (show boundarySize (p := p) packing items suffix store ≤
      SubexpNodeWorkerIterationBound.scale (p := p) packing items suffix store q ctx d from by
        unfold SubexpNodeWorkerIterationBound.scale preparedSize
        omega) hfull
  have hp : preparedSize (p := p) packing items suffix store q ≤ 20000000000 * S^16 := by
    apply le_trans (show preparedSize (p := p) packing items suffix store q ≤
      SubexpNodeWorkerIterationBound.scale (p := p) packing items suffix store q ctx d from by
        unfold SubexpNodeWorkerIterationBound.scale
        omega) hfull
  have hr0 := rawCommandCost_le e packing items suffix store
  have hr : SubexpRawTemplate.commandCost packing node items suffix
      (SubexpNodeBankBounds.outerBanks e) (SubexpNodeBankBounds.innerBanks e) store + 1 ≤
      envelope S J X := by
    apply le_trans hr0
    calc
      _ ≤ 167042000000 * (20000000000 * S^16)^8 * J^4 := by gcongr
      _ = (167042000000 * 20000000000^8) * S^128 * J^4 := by ring
      _ ≤ envelope S J X := promote S J X _ _ _ hS hJ hX raw_coefficient (by decide) (by decide)
  have ht0 := (template_bounds e packing items suffix store q preparation source preparedTarget
    minusOne hc bs hq hraw).1
  have ht : SubexpTemplateExecution.runCost preparation source preparedTarget minusOne bs ≤
      envelope S J X := by
    apply le_trans ht0
    calc
      _ ≤ 10^27 * (20000000000 * S^16)^13 * J^4 := by gcongr
      _ = (10^27 * 20000000000^13) * S^208 * J^4 := by ring
      _ ≤ envelope S J X := promote S J X _ _ _ hS hJ hX preparation_coefficient (by decide) (by decide)
  have hj0 := jobsPhaseCost_le_original source target cacheReduction cacheTheta R N hN width hw es
    scopes tables cache zero one C hC e heq hincidence hm hcache packing items suffix old226 store q
    hpackets h226 h227 preparation preparedTarget minusOne hc bs hq hraw ctx d hprepared M reduction z o
    slots inputs bytes expr htemplate hmaster hs hslots hbytes hsize
  have hj : jobsPhaseCost p ctx M reduction z o slots inputs bytes expr d ≤ envelope S J X := by
    apply hj0.trans
    unfold envelope
    have hpow :
        (originalScale (p := p) PacketStatic packing items suffix old226 q ctx d)^768 ≤ S^768 := by
      rw [show (768 : ℕ) = 192 * 4 by norm_num]
      simpa only [pow_mul] using Nat.pow_le_pow_left (Nat.pow_le_pow_left hOS 192) 4
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_left _ hpow))
  have hcleanup := cache_cleanup_le cleanup
  have hcS : cleanupInputSize cleanup ≤ S := by dsimp [S, scale]; omega
  have hpS : SubexpNodeTemplateReady.contextSize preparation ≤ S := by dsimp [S, scale]; omega
  have ha : SubexpNodeCacheSetup.cleanupCost cleanup +
      9 * SubexpNodeTemplateReady.contextSize preparation + 75 ≤ envelope S J X := by
    have hsmall : SubexpNodeCacheSetup.cleanupCost cleanup +
        9 * SubexpNodeTemplateReady.contextSize preparation + 75 ≤ 128 * S := by omega
    apply hsmall.trans
    simpa only [pow_one, pow_zero, Nat.mul_one] using
      promote S J X 128 1 0 hS hJ hX small_coefficient (by decide) (by decide)
  have hall : (SubexpRawTemplate.commandCost packing node items suffix
      (SubexpNodeBankBounds.outerBanks e) (SubexpNodeBankBounds.innerBanks e) store + 1) +
      SubexpTemplateExecution.runCost preparation source preparedTarget minusOne bs +
      SubexpNodeCacheSetup.cleanupCost cleanup + 9 * SubexpNodeTemplateReady.contextSize preparation + 75 +
      jobsPhaseCost p ctx M reduction z o slots inputs bytes expr d ≤ 4 * envelope S J X := by omega
  simpa only [envelope, S, J, X, Nat.mul_assoc] using hall

end SubexponentialSAT.SubexpNodeTemplateSuffixBound

end OAI.Algorithms
