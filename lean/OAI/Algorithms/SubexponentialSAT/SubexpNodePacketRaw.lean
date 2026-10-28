import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFactorPacketCorrectness
import OAI.Algorithms.SubexponentialSAT.Subexp.RawTemplateRefinement

namespace OAI.Algorithms

/-! Actual packet production followed by actual bank/assignment-driven raw
template assembly. The typed raw stream is a conclusion of both executions;
there is no assumed packet stream, grouped-factor list, or source program. -/

namespace SubexponentialSAT.SubexpNodePacketRaw

open BitProgram StructuredCalls SubexpSelectedConversions
open Subexp.ConstructivePacking

abbrev Data := State 16 288

attribute [local simp] Fin.coe_ofNat_eq_mod

variable {p D r Q Δ : ℕ} [Fact p.Prime] {F : Type*}
  (source : Prepared p 0) (target : Prepared p D)
  (theta : SubexpFactorPacketProvenance.Code p D)
  (order : List F) (factor : F → SubexpFactorPacketCorrectness.FactorInput p D)
  (word : F → MulticolorTypes.Word r Q)

def packet (f : F) : SubexpTemplateFactors.Factor p D :=
  SubexpFactorPacketProvenance.blueprintRows source target theta (factor f).data

def items := Subexp.RawTemplateRefinement.items order word (packet source target theta factor)

theorem packet_bytes :
    Encoding.encodeList Subexp.FactorBlueprint.encodeRows
        (SubexpFactorPacketCorrectness.typedFactors source target theta (order.map factor)) =
      Encoding.encodeList id ((items source target theta order factor word).map Prod.snd) := by
  simp only [SubexpFactorPacketCorrectness.typedFactors, items,
    Subexp.RawTemplateRefinement.items, List.map_map, Function.comp_def,
    SubexpBlueprintRows.encodeList_map, SubexpTemplateFactors.encode, packet, id_eq]

structure Masters
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (node : Fin Q) (suffix : List Bool) (d : Data) : Prop where
  assignment : d.stacks 258 =
    SubexpFactorRoutingTraversal.words (items source target theta order factor word) ++ suffix
  node : d.stacks 116 = List.replicate node.val true
  colors : d.stacks 261 = List.replicate r true
  width : (d.stacks 260).length = Q*r
  dimension : d.stacks 109 = List.replicate D true
  metadata : d.stacks 269 = Subexp.SupportSelectionProgram.metadataTable P

theorem ready_after_packets (d e : Data) (bits : List Bool)
    (he : e.stacks = Function.update (Function.update d.stacks 227 []) 225 bits)
    (hr : SubexpRawTemplate.Ready d.stacks) : SubexpRawTemplate.Ready e.stacks := by
  refine {
    toColorWork := {
      workspace := ?_
      bank := by simpa [he] using hr.bank
      payload := by simpa [he] using hr.payload
      support := by simpa [he] using hr.support
      factors := by simpa [he] using hr.factors
      term := by simpa [he] using hr.term
      terms := by simpa [he] using hr.terms
      group := by simpa [he] using hr.group
      scratch := by simpa [he] using hr.scratch
      outside := by simpa [he] using hr.outside
      forward := by simpa [he] using hr.forward }
    bases := by simpa [he] using hr.bases
    outsideMaster := by simpa [he] using hr.outsideMaster
    groupRecords := by simpa [he] using hr.groupRecords
    groups := by simpa [he] using hr.groups
    block := by simpa [he] using hr.block
    color := by simpa [he] using hr.color
    blocks := by simpa [he] using hr.blocks
    output := by simpa [he] using hr.output }
  intro i hlo hhi
  have h225 : i ≠ 225 := by intro h; subst i; norm_num at hhi
  have h227 : i ≠ 227 := by intro h; subst i; norm_num at hhi
  simpa [he,h225,h227] using hr.workspace i hlo hhi

variable (cache : List (List (SubexpFactorPacketProvenance.Code p D)))
  (modulus : List Bool) (zero one : SubexpFactorPacketProvenance.Code p D)

theorem program_runs
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (node : Fin Q) (suffix : List Bool)
    (bases : List (Fin D → ZMod p)) (increments : Fin r → List (Fin D → ZMod p))
    (d : Data)
    (hpacket : SubexpFactorPacketProgram.Ready d
      (SubexpFactorPacketCorrectness.physicalInputs source target theta cache modulus zero one
        (order.map factor)))
    (hp : BinaryArithmetic.toNat modulus = p) (hcache : p ≤ cache.length)
    (hc : ∀ f ∈ order, (factor f).data.cache = cache)
    (hlen : ∀ f ∈ order, (factor f).answers.length = p^(factor f).scope.length)
    (hrows : ∀ f ∈ order, (factor f).data.rows =
      SubexpRankedTable.attachAnswers zero one (factor f).answers)
    (hm : Masters source target theta order factor word P node suffix d)
    (hr : SubexpRawTemplate.Ready d.stacks)
    (hbanks : d.stacks 204 = SubexpRawTemplate.bankBundle
      (bases.map Subexp.RawTemplateRefinement.vectorBytes)
      (List.ofFn fun g => (increments g).map Subexp.RawTemplateRefinement.vectorBytes)) :
    ∃ (mid out : Data),
      RunsIn SubexpFactorPacketProgram.program
        (SubexpFactorPacketProgram.runtimeBound
          (SubexpFactorPacketCorrectness.physicalInputs source target theta cache modulus zero one
            (order.map factor)))
        (d.withPC (some SubexpFactorPacketProgram.program.entry)) (mid.withPC none) ∧
      RunsIn SubexpRawTemplate.program
        (SubexpRawTemplate.commandCost P node (items source target theta order factor word) suffix
          (bases.map Subexp.RawTemplateRefinement.vectorBytes)
          (List.ofFn fun g => (increments g).map Subexp.RawTemplateRefinement.vectorBytes)
          mid.stacks + 1)
        (mid.withPC (some SubexpRawTemplate.program.entry)) (out.withPC none) ∧
      out.stacks = SubexpRawTemplate.resultStore d.stacks
        (SubexpTemplateProgram.encodeBlocks
          ((Subexp.RawTemplateRefinement.blocks P node order word
            (packet source target theta factor) bases increments).map SubexpTemplateData.rawBlock)) := by
  have hc' : ∀ f ∈ order.map factor, f.data.cache = cache := by
    intro f hf
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hf
    exact hc a ha
  have hl' : ∀ f ∈ order.map factor, f.answers.length = p^f.scope.length := by
    intro f hf
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hf
    exact hlen a ha
  have hr' : ∀ f ∈ order.map factor, f.data.rows =
      SubexpRankedTable.attachAnswers zero one f.answers := by
    intro f hf
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hf
    exact hrows a ha
  obtain ⟨mid,ht,hs⟩ := SubexpFactorPacketCorrectness.program_runs_typed
    source target theta cache modulus zero one (order.map factor) d hpacket hp hcache hc' hl' hr'
  rw [packet_bytes source target theta order factor word] at hs
  have hmasters : SubexpRawTemplate.Masters P node
      (items source target theta order factor word) suffix mid.stacks := by
    constructor
    · simpa [hs] using hm.assignment
    · simp [hs]
    · simpa [hs] using hm.node
    · simpa [hs] using hm.colors
    · simpa [hs] using hm.width
    · simpa [hs] using hm.dimension
    · simpa [hs] using hm.metadata
  have hready' : SubexpRawTemplate.Ready mid.stacks := ready_after_packets d mid _ hs hr
  have hbanks' : mid.stacks 204 = SubexpRawTemplate.bankBundle
      (bases.map Subexp.RawTemplateRefinement.vectorBytes)
      (List.ofFn fun g => (increments g).map Subexp.RawTemplateRefinement.vectorBytes) := by
    simpa [hs] using hbanks
  obtain ⟨out,ho,hos⟩ := SubexpRawTemplate.program_runs P node
    (items source target theta order factor word) suffix
    (bases.map Subexp.RawTemplateRefinement.vectorBytes)
    (List.ofFn fun g => (increments g).map Subexp.RawTemplateRefinement.vectorBytes)
    (by simp) mid hmasters hready' hbanks'
  refine ⟨mid,out,ht,ho,?_⟩
  simp only [items] at hos
  rw [Subexp.RawTemplateRefinement.outputBytes_eq P node order word
    (packet source target theta factor) bases increments] at hos
  rw [hos,hs]
  funext i
  by_cases h225 : i = 225 <;> by_cases h227 : i = 227 <;>
    simp [SubexpRawTemplate.resultStore, Function.update_apply, h225, h227]

end SubexponentialSAT.SubexpNodePacketRaw

end OAI.Algorithms
