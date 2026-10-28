import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeWorkerBoundedExecution
import OAI.Algorithms.SubexponentialSAT.Subexp.NodeCanonicalScale

namespace OAI.Algorithms

/-! Actual worker execution bounded by original selected input words.
The cache, matrix, template, source and query streams are generated inside
the proved execution; none is a supplied size or runtime certificate. -/

namespace SubexponentialSAT.SubexpNodeWorkerMasterBound

private def coefficientBase : ℕ := 1000

def coefficient : ℕ :=
  7 * SubexpNodeOriginalInputBound.coefficient * (coefficientBase ^ 256) ^ 3

private theorem power_substitution (A S D J n : ℕ)
    (hA : A ≤ 1000*S^4)
    (hn : n ≤ 7*SubexpNodeOriginalInputBound.coefficient*A^768*2^(128*D)*J^8) :
    n ≤ coefficient*S^3072*2^(128*D)*J^8 := by
  have hA' : A ≤ coefficientBase * S ^ 4 := by
    simpa only [coefficientBase] using hA
  have hpower : ((coefficientBase * S ^ 4) ^ 256) ^ 3 =
      (coefficientBase ^ 256) ^ 3 * S ^ 3072 := by
    calc
      _ = (coefficientBase ^ 256 * (S ^ 4) ^ 256) ^ 3 := by rw [mul_pow]
      _ = (coefficientBase ^ 256) ^ 3 * ((S ^ 4) ^ 256) ^ 3 := by rw [mul_pow]
      _ = (coefficientBase ^ 256) ^ 3 * S ^ 3072 := by
        congr 1
        calc
          ((S ^ 4) ^ 256) ^ 3 = (S ^ 4) ^ (256 * 3) := (pow_mul _ _ _).symm
          _ = S ^ (4 * (256 * 3)) := (pow_mul _ _ _).symm
          _ = S ^ 3072 := by rw [show (4 : ℕ) * (256 * 3) = 3072 by decide]
  have hpowA : A ^ 768 ≤ (coefficientBase ^ 256) ^ 3 * S ^ 3072 := by
    calc
      _ = (A ^ 256) ^ 3 := by
        rw [show (768 : ℕ) = 256 * 3 by decide, pow_mul]
      _ ≤ ((coefficientBase * S ^ 4) ^ 256) ^ 3 :=
        Nat.pow_le_pow_left (Nat.pow_le_pow_left hA' 256) 3
      _ = _ := hpower
  have hbound := Nat.mul_le_mul_right (J ^ 8)
    (Nat.mul_le_mul_right (2 ^ (128 * D))
      (Nat.mul_le_mul_left (7 * SubexpNodeOriginalInputBound.coefficient) hpowA))
  exact hn.trans (by
    simpa only [coefficient, Nat.mul_assoc] using hbound)

abbrev Data := StructuredProgram.State 16 288

open BitProgram StructuredCalls SubexpLiftRing SubexpSelectedConversions
open SubexpNodeWorkspace SubexpNodeStoreTransitions SubexpNodeContexts
open MulticolorTypes Subexp.ConstructivePacking Subexp.BlockSearch
open Subexp.GlobalBasisRefinement (pairs packingLocation)
open SubexpMomentSourceProgram SubexpMomentSourceSemantics SubexpSymbolicCost

variable {p r Δ D k : ℕ} {τ : ℚ} [Fact p.Prime] [codeOne : One (QuarticCode p D)]
variable {F E : Type*} [Fintype F] [Field E] [Algebra (ZMod p) E]
variable {pattern : Factor.Pattern (Fin D) F}
variable {c : SubexpLayoutSpec.Parameters p k Δ r τ}
variable {L : SubexpLayoutSpec.Layout (E := E) pattern c}
variable
  (C : Subexp.GlobalBasisInput.Context p r c.Q Δ) (e : SubexpLayoutSpec.EnumerationData L C.position) (hr : 0 < r) (hQ : 0 < c.Q)
  (hsplit : ∀ g, (C.tables g).split ≤ (C.tables g).dimension)
  {m : Fin r → ℕ}
  (constraint : ∀ g, Fin (m g) → Fin (C.tables g).dimension → ZMod p)
  (good : ∀ g, GoodPair (constraint g) (pairs C hsplit g))
  (alphabet : List (ZMod p)) (complete : ∀ x, x ∈ alphabet)
  (P : PackingData (Fin D) (UniversalType r c.Q Δ))
  (masters : Store) (source : Prepared p 0) (target : Prepared p D)
  (minusOne : SubexpQuarticRing.Word (baseWidth p (D+1)))
  (hm : SubexpNodeContextSemantics.Masters masters source target minusOne)
  (theta : SubexpTaylorRow.Code p (D+1)) (R : ℕ)
  (cache : List (List (SubexpFactorPacketProvenance.Code p D)))
  (expr : ℕ → ℕ → ℕ → SubexpTaylorRowCorrectness.RowExpr p)
  (scopes : List (List ℕ)) (tables : List (List Bool))
  (words : Fin scopes.length → MulticolorTypes.Word r c.Q)

local notation "bases" => List.ofFn e.outerBase
local notation "increments" => fun g => List.ofFn (e.increment g)
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


/-- Original selected master fields and packet inputs; generated matrix,
Taylor-cache, template, source, and moment streams are absent. -/
noncomputable def inputSize (i : Fin (p^4-1)) : ℕ :=
  Subexp.NodeCanonicalScale.originalSize p D R r c.Q (rows).length masters
    (SubexpNodeIndexSemantics.thetaWord p D i) (SubexpNodeIndexSemantics.thetaWord p D i)
    (List.replicate C.position.val true)
    (SubexpNodeLiftData.liftedNodeWords p (D+1) source.modulus)
    source.modulus.bits (SubexpQuarticFlatNeg.flat target.zero) (SubexpQuarticFlatNeg.flat target.one)
    scopes tables (cache.map (List.map SubexpQuarticFlatNeg.flat))

theorem program_runs_original
    (htables : tables.length = scopes.length)
    (hanswers : ∀ e : Fin scopes.length, (tables.getD e.val []).length = p^(scopes.get e).length)
    (hcache : p ≤ cache.length)
    (harrays : (matrices).map (fun A => Subexp.MatrixImageEnumeration.bankRecords p A.entries) =
      SubexpNodeBankBounds.outerBanks e :: SubexpNodeBankBounds.innerBanks e)
    (before : List (List Bool)) (tail suffix : List Bool)
    (H : SubexpNodeBasisWorkspace.Masters C P.blockCount P.leftovers.length D before tail masters)
    (T : SubexpNodeBlueprintWorkspace.PacketMasters masters scopes tables
      (cache.map (List.map SubexpQuarticFlatNeg.flat))
      (SubexpQuarticFlatNeg.flat target.zero) (SubexpQuarticFlatNeg.flat target.one))
    (hmeta : C.metadata = Subexp.PackingMetadata.records P
      (fun v => Subexp.PackingMetadata.unary v.val) Subexp.CollisionProgram.encodeType)
    (hassignment : masters 258 = SubexpFactorRoutingTraversal.words items ++ suffix)
    (hwordwidth : (masters 260).length = c.Q*r)
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
    ∃ (indexState basisState rawState templateState out : Data) (n : ℕ)
      (sourceBytes : List Bool → List Bool)
      (actual : (Fin D → ℕ) → List (SubexpBlockAssemblySemantics.Block (QuarticCode p D) (Raw p D))),
      n ≤ coefficient * (inputSize C masters source target R cache expr scopes tables i)^3072 *
          2^(128*D) * (e.iterationCount+1)^8 ∧
      Trace SubexpNodeConcretePipeline.worker n
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
      indexState.stacks = indexed masters (SubexpNodeIndexSemantics.thetaWord p D i)
        cacheBytes (List.replicate C.position.val true) ∧
      templateState.stacks = templated masters (List.replicate C.position.val true) templateBytes ∧
      rawState.stacks = raw masters (SubexpNodeIndexSemantics.thetaWord p D i) cacheBytes
        (List.replicate C.position.val true)
        (SubexpTemplateProgram.encodeBlocks ((blocks).map SubexpTemplateData.rawBlock)) ∧
      basisState.stacks = Function.update indexState.stacks 201
        (ProgramEncoding.encodeRecords ((matrices).map SubexpNodeBankMap.payload)) := by
  let _ : One (QuarticCode p (Ctx).dimension) := codeOne
  let _ (bits : List Bool) : One (QuarticCode p ((Ctx).withExponent bits).dimension) := codeOne
  obtain ⟨indexState,basisState,rawState,templateState,out,n,sourceBytes,actual,
    hn,htrace,hout,hrel,hbytes,hsize,hindex,htemplated,hraw,hbasis⟩ :=
    SubexpNodeWorkerBoundedExecution.program_runs_bounded C e hr hQ hsplit constraint good
      alphabet complete P masters source target minusOne hm theta R cache expr scopes tables words
      htables hanswers hcache harrays before tail suffix H T hmeta hassignment hwordwidth hD hI hmetadata
      h126 h255 h125 h127 hzero hone hcanonical hslots hreduction reference hprovenance i hposition htheta d hactive
  have hactiveLocal : (SubexpNodeCacheIndex.localState d).stacks =
      activeStacks masters (SubexpNodeIndexSemantics.thetaWord p D i) ∘ Fin.castAdd 32 := by
    funext j
    exact congrFun hactive (Fin.castAdd 32 j)
  have hrawLocal : (SubexpNodeTemplatePipeline.localState rawState).stacks =
      raw masters (SubexpNodeIndexSemantics.thetaWord p D i) cacheBytes
        (List.replicate C.position.val true)
        (SubexpTemplateProgram.encodeBlocks ((blocks).map SubexpTemplateData.rawBlock)) ∘ Fin.castAdd 32 := by
    funext j
    exact congrFun hraw (Fin.castAdd 32 j)
  have hframe (j : Fin 288) (hj : 255 ≤ j.val) : basisState.stacks j = masters j := by
    have hne : j ≠ 201 := by
      intro he
      subst j
      change 255 ≤ 201 at hj
      omega
    rw [hbasis, Function.update_of_ne hne, hindex]
    exact SubexpNodeBasisWorkspace.indexed_master masters _ _ _ j hj
  have hscale := Subexp.NodeCanonicalScale.combinedScale_le p D R r c.Q Δ (rows).length
    masters (SubexpNodeIndexSemantics.thetaWord p D i) (SubexpNodeIndexSemantics.thetaWord p D i)
    (List.replicate C.position.val true)
    (SubexpNodeLiftData.liftedNodeWords p (D+1) source.modulus)
    source.modulus.bits (SubexpQuarticFlatNeg.flat target.zero) (SubexpQuarticFlatNeg.flat target.one)
    scopes tables (cache.map (List.map SubexpQuarticFlatNeg.flat)) P items suffix
    target.modulus target.reduction theta (SubexpNodeCacheTyped.rows p (D+1) source R rows)
    (by simpa only [SubexpNodeCacheTyped.rows_length] using (le_refl (rows).length))
    (SubexpNodeCacheTyped.rows_width p (D+1) source R D rows
      (SubexpNodeBlueprintExecution.row_width expr D 0 scopes))
    cacheBytes (SubexpTemplateProgram.encodeBlocks ((blocks).map SubexpTemplateData.rawBlock)) templateBytes
    (SubexpNodeCacheTyped.cache_bytes p (D+1) source target.modulus target.reduction theta R (R+1) rows).symm
    (SubexpNodeCacheIndex.localState d) (SubexpNodeTemplatePipeline.localState rawState)
    indexState basisState templateState hactiveLocal hindex hrawLocal htemplated
    (hframe 279 (by decide)) (hframe 277 (by decide))
    (hframe 280 (by decide)) (hframe 264 (by decide))
    H.modulus H.zeroWord H.tokens hassignment hmetadata
  have hscale' : SubexpNodeWorkerNumericalBound.scale C e P masters source target minusOne hm theta R
      cache expr scopes tables words suffix (SubexpNodeIndexSemantics.thetaWord p D i)
      (SubexpNodeLiftData.liftedNodeWords p (D+1) source.modulus)
      d indexState basisState rawState templateState ≤
      1000 * (inputSize C masters source target R cache expr scopes tables i)^4 := by
    simpa only [SubexpNodeWorkerNumericalBound.scale, inputSize] using hscale
  exact ⟨indexState,basisState,rawState,templateState,out,n,sourceBytes,actual,
    power_substitution _ _ D (e.iterationCount+1) n hscale' hn,
    htrace,hout,hrel,hbytes,hsize,hindex,htemplated,hraw,hbasis⟩

end SubexponentialSAT.SubexpNodeWorkerMasterBound

end OAI.Algorithms
