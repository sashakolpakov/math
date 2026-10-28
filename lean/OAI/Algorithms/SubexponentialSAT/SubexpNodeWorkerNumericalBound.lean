import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodePipelineBound
import OAI.Algorithms.SubexponentialSAT.SubexpNodeWorkerExecution
import OAI.Algorithms.SubexponentialSAT.SubexpRawTemplateTaylorBound

namespace OAI.Algorithms

/-! Specialize the complete numeric pipeline bound to the node worker's
actual row traversal, factor packets, raw blocks, and source (inputs). Every
packet alignment, Taylor-column bound, and serialized-template identity is
derived from these constructors. -/

namespace SubexponentialSAT.SubexpNodeWorkerNumericalBound

open BitProgram StructuredCalls SubexpLiftRing SubexpSelectedConversions
open SubexpNodeWorkspace SubexpNodeStoreTransitions SubexpNodeContexts
open MulticolorTypes Subexp.ConstructivePacking Subexp.BlockSearch
open Subexp.GlobalBasisRefinement (pairs packingLocation)
open SubexpMomentSourceProgram SubexpMomentSourceSemantics SubexpSymbolicCost
open SubexpNodeBankBounds

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Data := State 16 288

variable {p D k Δ r : ℕ} {τ : ℚ} [Fact p.Prime]
variable {F E : Type*} [Fintype F] [Field E] [Algebra (ZMod p) E]
variable {pattern : Factor.Pattern (Fin D) F}
variable {c : SubexpLayoutSpec.Parameters p k Δ r τ}
variable {L : SubexpLayoutSpec.Layout (E := E) pattern c}

theorem bankBundle_eq {node : Fin c.Q} (e : SubexpLayoutSpec.EnumerationData L node)
    (matrices : List (SubexpNodeBankMap.Matrix p D))
    (harrays : matrices.map (fun A => Subexp.MatrixImageEnumeration.bankRecords p A.entries) =
      outerBanks e :: innerBanks e) :
    ProgramEncoding.encodeRecords (matrices.map SubexpNodeBankMap.bankList) =
      SubexpRawTemplate.bankBundle
        ((List.ofFn e.outerBase).map Subexp.RawTemplateRefinement.vectorBytes)
        (List.ofFn fun g => (List.ofFn (e.increment g)).map Subexp.RawTemplateRefinement.vectorBytes) := by
  have h := congrArg ProgramEncoding.encodeRecords
    (congrArg (List.map ProgramEncoding.encodeRecords) harrays)
  have hb (A : SubexpNodeBankMap.Matrix p D) :
      ProgramEncoding.encodeRecords (Subexp.MatrixImageEnumeration.bankRecords p A.entries) =
        SubexpNodeBankMap.bankList A := rfl
  have hv (vs : List (Fin D → ZMod p)) :
      vs.map (SubexpNodeBankBounds.vectorBytes p) =
        vs.map Subexp.RawTemplateRefinement.vectorBytes := by
    apply List.map_congr_left
    intro v _
    rfl
  have hinner :
      (List.ofFn fun g : Fin r =>
          (List.ofFn (e.increment g)).map (SubexpNodeBankBounds.vectorBytes p)) =
        List.ofFn fun g : Fin r =>
          (List.ofFn (e.increment g)).map Subexp.RawTemplateRefinement.vectorBytes := by
    apply congrArg List.ofFn
    funext g
    exact hv _
  simp only [List.map_map, List.map_cons, Function.comp_def,
    SubexpNodeBankBounds.outerBanks, SubexpNodeBankBounds.innerBanks,
    SubexpNodeBankBounds.bank, hb] at h
  rw [hv, hinner] at h
  simpa only [SubexpRawTemplate.bankBundle] using h

variable (C : Subexp.GlobalBasisInput.Context p r c.Q Δ)
  (e : SubexpLayoutSpec.EnumerationData L C.position)
  (P : PackingData (Fin D) (UniversalType r c.Q Δ))
  (masters : Store) (source : Prepared p 0) (target : Prepared p D)
  (minusOne : SubexpQuarticRing.Word (baseWidth p (D+1)))
  (hm : SubexpNodeContextSemantics.Masters masters source target minusOne)
  (theta : SubexpTaylorRow.Code p (D+1)) (R : ℕ)
  (cache : List (List (SubexpFactorPacketProvenance.Code p D)))
  (rowExpr : ℕ → ℕ → ℕ → SubexpTaylorRowCorrectness.RowExpr p)
  (scopes : List (List ℕ)) (tables : List (List Bool))
  (words : Fin scopes.length → Word r c.Q)

local notation "rows" => SubexpDenseRowTableSemantics.expressionRows rowExpr D 0 scopes
local notation "factor" => SubexpNodePacketInputs.factor source target theta R (masters 129)
  hm.sourceWidth cache target.zero target.one rowExpr scopes tables
local notation "order" => List.finRange scopes.length
local notation "items" => SubexpNodePacketRaw.items source target theta order factor words
local notation "bases" => List.ofFn e.outerBase
local notation "increments" => fun g => List.ofFn (e.increment g)
local notation "blocks" => Subexp.RawTemplateRefinement.blocks P C.position order words
  (SubexpNodePacketRaw.packet source target theta factor) bases increments
local notation "blocksGood" => Subexp.RawTemplateRefinement.blocks_good P C.position order words
  (SubexpNodePacketRaw.packet source target theta factor) bases increments
local notation "TC" => templateContext masters D
local notation "templateBytes" => SubexpTemplateExecution.output TC source target minusOne blocks
local notation "Ctx" => sourceContext masters D templateBytes
local notation "inputs" => SubexpNodeTemplateMoment.inputs masters source target minusOne hm blocks blocksGood
local notation "flatCache" => cache.map (List.map SubexpQuarticFlatNeg.flat)
local notation "flatZero" => SubexpQuarticFlatNeg.flat target.zero
local notation "flatOne" => SubexpQuarticFlatNeg.flat target.one
local notation "Packet" => SubexpFactorPacketCorrectness.physicalInputs source target theta cache
  source.modulus.bits target.zero target.one (List.map factor order)
local notation "ReadyInput" => SubexpNodePacketReady.inputs p (D+1) source target.modulus
  target.reduction theta R (R+1) (Nat.succ_pos R) (masters 129) hm.sourceWidth rows
  scopes tables flatCache flatZero flatOne
local notation "PacketStatic" => SubexpNodePacketInputBound.staticSize p (D+1) R (R+1) D (List.length rows)
  source.modulus.bits flatZero flatOne scopes tables flatCache

variable [codeOne : One (QuarticCode p D)]
local instance : Zero (Raw p D) := ⟨[]⟩
local instance : One (Raw p D) := ⟨SubexpAlgorithm.rawOne D⟩
local instance : One (QuarticCode p (Ctx).dimension) := codeOne

/-- The bound's scale names only the original packet masters and the
selected physical state fields. Canonical-state substitution is separate. -/
abbrev scale (suffix query : List Bool) (nodes : List (List Bool))
    (initial indexState basisState rawState templateState : Data) : ℕ :=
  SubexpNodeCostAssembly.scale
    (Subexp.NodePreludeSum.scale p D (rows).length D R (R+1)
      (baseWidth p (D+1)) (baseWidth p 1) source.modulus.bits.length
      (SubexpNodeCacheIndex.localState initial) query nodes indexState basisState)
    PacketStatic
    (SubexpNodeTemplateSuffixBound.scale (p := p) PacketStatic P items suffix [] (R+1)
      Ctx templateState (SubexpNodeTemplatePipeline.localState rawState) TC)

/-- Literal sum of the worker's actual component budgets, including all
outer halts. The source/interpreter terms refer to the produced expression. -/
def cost (suffix query : List Bool) (nodes : List (List Bool))
    (matrices : List (SubexpNodeBankMap.Matrix p D))
    (initial indexState basisState packetState rawState templateState : Data)
    (sourceBytes : List Bool → List Bool)
    (actual : (Fin D → ℕ) → List (SubexpBlockAssemblySemantics.Block
      (QuarticCode p D) (Raw p D))) : ℕ :=
  let : One (QuarticCode p (Ctx).dimension) := codeOne
  Subexp.NodePreludeSum.cost (rows).length D R (R+1) (baseWidth p (D+1)) (baseWidth p 1)
    source.modulus.bits.length (SubexpNodeCacheIndex.localState initial) query nodes C
    P.blockCount P.leftovers.length (List.ofFn (packingLocation P)) indexState basisState matrices +
  SubexpFactorPacketProgram.runtimeBound Packet +
  ((SubexpRawTemplate.commandCost P C.position items suffix (outerBanks e) (innerBanks e)
      packetState.stacks + 1) +
    SubexpTemplateExecution.runCost TC source target minusOne blocks +
    SubexpNodeCacheSetup.cleanupCost (SubexpNodeTemplatePipeline.localState rawState) +
    9 * SubexpNodeTemplateReady.contextSize TC + 75 +
    SubexpNodeWorkerBound.jobsPhaseCost p Ctx target.modulus target.reduction target.zero 1
      (SubexpQueryOrder.visitSlots D) inputs sourceBytes
      (SubexpNodeSourceJobs.expression p Ctx actual) templateState) + 1

theorem cost_le
    (htables : tables.length = scopes.length)
    (hanswers : ∀ f : Fin scopes.length, (tables.getD f.val []).length = p^(scopes.get f).length)
    (hcache : p ≤ cache.length)
    (suffix query : List Bool) (nodes : List (List Bool))
    (matrices : List (SubexpNodeBankMap.Matrix p D))
    (harrays : matrices.map (fun A => Subexp.MatrixImageEnumeration.bankRecords p A.entries) =
      outerBanks e :: innerBanks e)
    (before : List (List Bool)) (tail : List Bool)
    (H : SubexpNodeBasisWorkspace.Masters C P.blockCount P.leftovers.length D before tail masters)
    (hmeta : C.metadata = Subexp.PackingMetadata.records P
      (fun v => Subexp.PackingMetadata.unary v.val) Subexp.CollisionProgram.encodeType)
    (initial indexState basisState originState packetState rawState templateState : Data)
    (node cacheBytes : List Bool)
    (hindex : indexState.stacks = indexed masters node cacheBytes (List.replicate C.position.val true))
    (horigin : originState.stacks = SubexpNodeBasisBankOrigin.finishedStacks indexState.stacks
      (ProgramEncoding.encodeRecords (matrices.map SubexpNodeBankMap.bankList))
      (SubexpNodeOriginExecution.output p (D+1) source target.modulus target.reduction theta
        R (R+1) (Nat.succ_pos R) source.modulus (masters 129) hm.sourceWidth rows))
    (hpacket : packetState.stacks = Function.update (Function.update originState.stacks 227 []) 225
      (Encoding.encodeList id ((items).map Prod.snd)))
    (htemplated : templateState.stacks = templated masters (List.replicate C.position.val true) templateBytes)
    (h127 : masters 127 = Encoding.encodeList id (SubexpOuterJobs.momentRecords D))
    (sourceBytes : List Bool → List Bool)
    (actual : (Fin D → ℕ) → List (SubexpBlockAssemblySemantics.Block
      (QuarticCode p D) (Raw p D)))
    (hbytes : letI : One (QuarticCode p (Ctx).dimension) := codeOne
      ∀ a : Fin D → ℕ, sourceBytes (SubexpExponentController.momentWord a) =
      SubexpPostfixControl.serializeCode (SubexpDenseSerialization.encodeFixedQuarticCoefficients p D)
        (SubexpNodeSourceJobs.expression p Ctx actual a).compile)
    (hsize : letI : One (QuarticCode p (Ctx).dimension) := codeOne
      ∀ a : Fin D → ℕ, (sourceBytes (SubexpExponentController.momentWord a)).length ≤
      uniformSourceBytes Ctx inputs) :
    cost C e P masters source target minusOne hm theta R cache rowExpr scopes tables words
      suffix query nodes matrices initial indexState basisState packetState rawState templateState sourceBytes actual ≤
      7 * SubexpNodeOriginalInputBound.coefficient *
        (scale C e P masters source target minusOne hm theta R cache rowExpr scopes tables words
          suffix query nodes initial indexState basisState rawState templateState)^768 *
        2^(128*D) * (e.iterationCount+1)^8 := by
  let : One (QuarticCode p (Ctx).dimension) := codeOne
  have hi : ReadyInput = Packet := SubexpNodePacketInputs.inputs_eq_physicalInputs
    source target theta R (masters 129) hm.sourceWidth cache target.zero target.one
      rowExpr scopes tables htables
  have halign := SubexpFactorPacketCorrectness.physical_alignment source target theta cache
    source.modulus.bits target.zero target.one ((order).map factor)
  have hp : BinaryArithmetic.toNat source.modulus.bits = p := by
    simpa only [Nat.zero_add, pow_one] using source.modulus.value
  have hpositive : 0 < BinaryArithmetic.toNat (ReadyInput).modulus := by
    change 0 < BinaryArithmetic.toNat source.modulus.bits
    rw [hp]
    exact (Fact.out : p.Prime).pos
  have hcache' : BinaryArithmetic.toNat (ReadyInput).modulus ≤ (ReadyInput).cache.length := by
    simpa only [SubexpNodePacketReady.inputs, List.length_map, hp] using hcache
  have hpackets : Encoding.encodeList id ((items).map Prod.snd) =
      SubexpFactorPacketProgram.output ReadyInput := by
    rw [hi, SubexpFactorPacketCorrectness.output_eq_typedFactors source target theta cache
      source.modulus.bits target.zero target.one ((order).map factor) hp]
    · exact (SubexpNodePacketRaw.packet_bytes source target theta order factor words).symm
    · intro f hf
      obtain ⟨f,_,rfl⟩ := List.mem_map.mp hf
      rfl
    · intro f hf
      obtain ⟨f,_,rfl⟩ := List.mem_map.mp hf
      exact hanswers f
    · intro f hf
      obtain ⟨f,_,rfl⟩ := List.mem_map.mp hf
      rfl
  have h226 : packetState.stacks 226 = [] := by
    rw [hpacket, horigin, hindex]
    exact (SubexpNodeCanonicalCostInputs.packet_scratch masters node cacheBytes
      (List.replicate C.position.val true) _ _ _).1
  have h227 : packetState.stacks 227 = [] := by simp [hpacket]
  have hraw : SubexpTemplateProgram.encodeBlocks ((blocks).map SubexpTemplateData.rawBlock) =
      SubexpRawTemplate.outputBytes P C.position items (outerBanks e) (innerBanks e) :=
    (Subexp.RawTemplateRefinement.outputBytes_eq P C.position order words
      (SubexpNodePacketRaw.packet source target theta factor) bases increments).symm
  have hq := SubexpRawTemplateTaylorBound.node_blocks_taylorBound source target theta R
    (masters 129) hm.sourceWidth cache target.zero target.one rowExpr scopes tables
    P C.position words bases increments
  have htemplate : (Ctx).template = encodeTemplate ((inputs).map BlockData.template) :=
    (SubexpTemplateSourceData.blocksData_template_bytes Ctx hm.sourceWidth TC
      source target minusOne blocks blocksGood).symm
  have hmaster : templateState.stacks 127 =
      Encoding.encodeList id (SubexpOuterJobs.momentRecords D) := by
    simpa [htemplated, templated, initialStacks, MasterPort] using h127
  have hslots : (SubexpQueryOrder.visitSlots D).length ≤ slotCount D := by
    rw [SubexpQueryOrder.visitSlots_length]
    exact le_rfl
  have hBasis := SubexpNodeBasisWorkspace.input H hindex
  have hBasis' : SubexpNodeBasisExecution.Input C P.blockCount P.leftovers.length
      (List.ofFn (packingLocation P)).length before tail indexState := by
    simpa only [List.length_ofFn] using hBasis
  have h := SubexpNodePipelineBound.pipelineCost_le source target.modulus target.reduction theta
    R (R+1) (Nat.succ_pos R) (masters 129) hm.sourceWidth rows scopes tables flatCache flatZero flatOne
    D (SubexpNodeBlueprintExecution.row_width rowExpr D 0 scopes) e
    (by simpa only [hi] using halign.1) (by simpa only [hi] using halign.2.1)
    hpositive hcache' P items suffix [] packetState.stacks (R+1)
    hpackets h226 h227 TC target minusOne
    (SubexpNodeContextSemantics.template_good masters source target minusOne hm) blocks hq hraw
    Ctx templateState (SubexpNodeTemplatePipeline.localState rawState) rfl target.modulus
    target.reduction target.zero 1 (SubexpQueryOrder.visitSlots D) inputs sourceBytes
    (SubexpNodeSourceJobs.expression p Ctx actual) htemplate hmaster
    (fun a ha => (SubexpQueryOrder.mem_visitSlots D a).mp ha) hslots hbytes hsize
    matrices harrays (rows).length D R (R+1) (baseWidth p (D+1)) (baseWidth p 1)
    source.modulus.bits.length (SubexpNodeCacheIndex.localState initial) query nodes C
    P.blockCount P.leftovers.length (List.ofFn (packingLocation P)) before tail indexState basisState
    hBasis' (Subexp.GlobalBasisRefinement.packing_locations C P hmeta)
  rw [hi] at h
  have hdim : (Ctx).dimension = D := rfl
  have hdimPow : 2 ^ (128 * (Ctx).dimension) = 2 ^ (128 * D) :=
    congrArg (fun d : ℕ => 2 ^ (128 * d)) hdim
  rw [hdimPow] at h
  convert h using 1
  rfl

end SubexponentialSAT.SubexpNodeWorkerNumericalBound

end OAI.Algorithms
