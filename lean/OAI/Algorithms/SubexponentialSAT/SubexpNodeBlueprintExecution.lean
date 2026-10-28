import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeBlueprintWorkspace
import OAI.Algorithms.SubexponentialSAT.SubexpNodePacketInputs
import OAI.Algorithms.SubexponentialSAT.SubexpNodePacketRawEvidence
import OAI.Algorithms.SubexponentialSAT.SubexpNodeBlueprintStage

namespace OAI.Algorithms

/-! The five concrete blueprint calls, joined at their actual byte formats.
The shared row traversal determines both origin extraction and factor packet
inputs. All workspace assertions follow from the indexed node boundary. -/

namespace SubexponentialSAT.SubexpNodeBlueprintExecution

open BitProgram StructuredCalls SubexpLiftRing SubexpSelectedConversions
open SubexpNodeWorkspace SubexpNodeStoreTransitions
open MulticolorTypes Subexp.ConstructivePacking Subexp.BlockSearch
open Subexp.GlobalBasisRefinement (pairs packingLocation)

abbrev Data := State 16 288

theorem row_width {X : Type*} (expr : ℕ → ℕ → ℕ → X) (D start : ℕ)
    (scopes : List (List ℕ)) :
    ∀ row ∈ SubexpDenseRowTableSemantics.expressionRows expr D start scopes,
      row.length ≤ D := by
  induction scopes generalizing start with
  | nil => simp [SubexpDenseRowTableSemantics.expressionRows]
  | cons scope scopes ih =>
    intro row hr
    simp only [SubexpDenseRowTableSemantics.expressionRows, List.mem_append] at hr
    rcases hr with hr | hr
    · obtain ⟨v,_,rfl⟩ := List.mem_map.mp hr
      simp
    · exact ih (start+1) row hr

variable {p r Q Δ D : ℕ} [Fact p.Prime]
  (C : Subexp.GlobalBasisInput.Context p r Q Δ) (hr : 0 < r) (hQ : 0 < Q)
  (hsplit : ∀ g, (C.tables g).split ≤ (C.tables g).dimension)
  {m : Fin r → ℕ}
  (constraint : ∀ g, Fin (m g) → Fin (C.tables g).dimension → ZMod p)
  (good : ∀ g, GoodPair (constraint g) (pairs C hsplit g))
  (alphabet : List (ZMod p)) (complete : ∀ x, x ∈ alphabet)
  (P : PackingData (Fin D) (UniversalType r Q Δ))
  (source : Prepared p 0) (target : Prepared p D)
  (theta : SubexpTaylorRow.Code p (D+1))
  (R : ℕ) (sourceWidth : List Bool) (hw : sourceWidth.length = baseWidth p 1)
  (cache : List (List (SubexpFactorPacketProvenance.Code p D)))
  (expr : ℕ → ℕ → ℕ → SubexpTaylorRowCorrectness.RowExpr p)
  (scopes : List (List ℕ)) (tables : List (List Bool))
  (words : Fin scopes.length → Word r Q)

local notation "rows" => SubexpDenseRowTableSemantics.expressionRows expr D 0 scopes
local notation "cacheBytes" => SubexpOriginCacheSemantics.taylorBytes p (D+1) source
  target.modulus target.reduction theta R (R+1) rows
local notation "factor" => SubexpNodePacketInputs.factor source target theta R sourceWidth hw
  cache target.zero target.one expr scopes tables
local notation "order" => List.finRange scopes.length
local notation "items" => SubexpNodePacketRaw.items source target theta order factor words
local notation "matrices" => Subexp.GlobalBasisMatrixBytes.images C hr hQ hsplit
  constraint good alphabet complete P
local notation "origins" => SubexpNodeOriginExecution.output p (D+1) source target.modulus
  target.reduction theta R (R+1) (Nat.succ_pos R) source.modulus sourceWidth hw rows

theorem program_runs
    (htables : tables.length = scopes.length)
    (hanswers : ∀ e : Fin scopes.length, (tables.getD e.val []).length = p^(scopes.get e).length)
    (hcache : p ≤ cache.length)
    (bases : List (Fin D → ZMod p)) (increments : Fin r → List (Fin D → ZMod p))
    (hbank : ProgramEncoding.encodeRecords ((matrices).map SubexpNodeBankMap.bankList) =
      SubexpRawTemplate.bankBundle (bases.map Subexp.RawTemplateRefinement.vectorBytes)
        (List.ofFn fun g => (increments g).map Subexp.RawTemplateRefinement.vectorBytes))
    (before : List (List Bool)) (tail suffix node : List Bool)
    (masters : Store) (d : Data)
    (hstate : d.stacks = indexed masters node cacheBytes (List.replicate C.position.val true))
    (H : SubexpNodeBasisWorkspace.Masters C P.blockCount P.leftovers.length D before tail masters)
    (O : SubexpNodeBlueprintWorkspace.OriginMasters masters source.modulus.bits
      (masters 10) sourceWidth)
    (hwidth : (masters 10).length = baseWidth p (D+1))
    (T : SubexpNodeBlueprintWorkspace.PacketMasters masters scopes tables
      (cache.map (List.map SubexpQuarticFlatNeg.flat))
      (SubexpQuarticFlatNeg.flat target.zero) (SubexpQuarticFlatNeg.flat target.one))
    (hmeta : C.metadata = Subexp.PackingMetadata.records P
      (fun v => Subexp.PackingMetadata.unary v.val) Subexp.CollisionProgram.encodeType)
    (hassignment : masters 258 = SubexpFactorRoutingTraversal.words items ++ suffix)
    (hcolors : masters 261 = List.replicate r true)
    (hwordwidth : (masters 260).length = Q*r)
    (hD : masters 109 = List.replicate D true)
    (hmetadata : masters 269 = Subexp.SupportSelectionProgram.metadataTable P) :
    ∃ (afterBasis afterOrigin packetState out : Data) (n : ℕ),
      n ≤ SubexpNodeBasisExecution.runtimeBound C P.blockCount P.leftovers.length
          (List.ofFn (packingLocation P)) d +
        (SubexpNodeBankStage.budget afterBasis matrices + 1) +
        SubexpOriginMap.tableBound (rows).length D (baseWidth p (D+1))
          (baseWidth p 1) source.modulus.bits.length R +
        SubexpFactorPacketProgram.runtimeBound
          (SubexpFactorPacketCorrectness.physicalInputs source target theta cache source.modulus.bits
            target.zero target.one ((order).map factor)) +
        (SubexpRawTemplate.commandCost P C.position items suffix
          (bases.map Subexp.RawTemplateRefinement.vectorBytes)
          (List.ofFn fun g => (increments g).map Subexp.RawTemplateRefinement.vectorBytes)
          packetState.stacks + 1) + 1 ∧
      Trace SubexpNodeBlueprintStage.program n
        (d.withPC (some SubexpNodeBlueprintStage.program.entry)) (out.withPC none) ∧
      afterOrigin.stacks = SubexpNodeBasisBankOrigin.finishedStacks d.stacks
        (ProgramEncoding.encodeRecords ((matrices).map SubexpNodeBankMap.bankList)) origins ∧
      packetState.stacks = Function.update (Function.update afterOrigin.stacks 227 []) 225
        (Encoding.encodeList id ((items).map Prod.snd)) ∧
      out.stacks = raw masters node cacheBytes (List.replicate C.position.val true)
        (SubexpTemplateProgram.encodeBlocks
          ((Subexp.RawTemplateRefinement.blocks P C.position order words
            (SubexpNodePacketRaw.packet source target theta factor) bases increments).map
              SubexpTemplateData.rawBlock)) := by
  obtain ⟨afterBasis,afterBank,afterOrigin,nb,nk,no,hnb,hnk,hno,hb,hk,ho,_,_,hpkt,hs⟩ :=
    SubexpNodeBasisBankOrigin.stage_traces C hr hQ hsplit constraint good alphabet complete P
      source target.modulus target.reduction theta R (R+1) (Nat.succ_pos R) (Nat.succ_pos D)
      sourceWidth (masters 10) hw hwidth D rows (row_width expr D 0 scopes)
      scopes tables (cache.map (List.map SubexpQuarticFlatNeg.flat))
      (SubexpQuarticFlatNeg.flat target.zero) (SubexpQuarticFlatNeg.flat target.one)
      before tail d (SubexpNodeBasisWorkspace.input H hstate)
      (SubexpNodeBasisWorkspace.bankStatics H hstate) hmeta
      (SubexpNodeBlueprintWorkspace.originReady O hstate)
      (SubexpNodeBlueprintWorkspace.packetStatics T hstate)
  have packetReady := SubexpNodePacketInputs.ready source target theta R sourceWidth hw
    cache target.zero target.one expr scopes tables htables hpkt
  have hm : SubexpNodePacketRaw.Masters source target theta order factor words P C.position suffix afterOrigin := by
    constructor
    · rw [hs,hstate]
      exact hassignment
    · rw [hs,hstate]
      rfl
    · rw [hs,hstate]
      exact hcolors
    · rw [hs,hstate]
      exact hwordwidth
    · rw [hs,hstate]
      exact hD
    · rw [hs,hstate]
      exact hmetadata
  have rawReady : SubexpRawTemplate.Ready afterOrigin.stacks :=
    SubexpNodeBlueprintWorkspace.raw_ready_of_stacks (by rw [hs,hstate])
  have banks : afterOrigin.stacks 204 =
      SubexpRawTemplate.bankBundle (bases.map Subexp.RawTemplateRefinement.vectorBytes)
        (List.ofFn fun g => (increments g).map Subexp.RawTemplateRefinement.vectorBytes) := by
    rw [hs,SubexpNodeBasisBankOrigin.finished_banks]
    exact hbank
  have hp : BinaryArithmetic.toNat source.modulus.bits = p := by
    simpa using source.modulus.value
  obtain ⟨packetState,out,⟨np,hnp,htp⟩,⟨nr,hnr,htr⟩,hpack,hout⟩ :=
    SubexpNodePacketRaw.program_runs_with_packets source target theta order factor words cache
      source.modulus.bits target.zero target.one P C.position suffix bases increments afterOrigin
      packetReady hp hcache (fun _ _ => rfl) (fun e _ => hanswers e) (fun _ _ => rfl)
      hm rawReady banks
  refine ⟨afterBasis,afterOrigin,packetState,out,_,?_,
    SubexpNodeBlueprintStage.program_trace hb hk ho htp htr,hs,hpack,?_⟩
  · simp only [Nat.add_sub_cancel] at hno
    omega
  · rw [hout,hs,hstate,blueprint_result]

end SubexponentialSAT.SubexpNodeBlueprintExecution

end OAI.Algorithms
