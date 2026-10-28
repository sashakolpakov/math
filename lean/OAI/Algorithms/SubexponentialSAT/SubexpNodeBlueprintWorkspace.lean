import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeBasisWorkspace
import OAI.Algorithms.SubexponentialSAT.SubexpNodePacketReady

namespace OAI.Algorithms

/-! The canonical indexed node store supplies all remaining blueprint
workspace invariants. Only immutable master-byte identities are inputs. -/

namespace SubexponentialSAT.SubexpNodeBlueprintWorkspace

open BitProgram StructuredCalls
open SubexpNodeWorkspace (Store MasterPort initialStacks activeStacks)
open SubexpNodeStoreTransitions (cached indexed)
open SubexpNodeBasisBankOrigin (finishedStacks)

abbrev Data := State 16 288

structure OriginMasters (masters : Store) (modulus targetWidth sourceWidth : List Bool) : Prop where
  modulus : masters 128 = modulus
  targetWidth : masters 10 = targetWidth
  sourceWidth : masters 129 = sourceWidth

structure PacketMasters (masters : Store) (scopes : List (List ℕ))
    (tables : List (List Bool)) (lagrange : List (List (List Bool)))
    (zero one : List Bool) : Prop where
  scopes : masters 256 = Encoding.encodeList SubexpFactorPrefixProgram.scopeBytes scopes
  tables : masters 257 = Encoding.encodeList id tables
  lagrange : masters 284 = Subexp.FactorPacketCoordinates.cacheBytes lagrange
  zero : masters 119 = zero
  one : masters 120 = one

theorem indexed_master (masters : Store) (node cache index : List Bool)
    (i : Fin 288) (hi : MasterPort i) : indexed masters node cache index i = masters i := by
  have hn (j : Fin 288) (hj : ¬ MasterPort j) : i ≠ j := by
    intro he
    exact hj (he ▸ hi)
  simp only [indexed, cached, activeStacks,
    Function.update_of_ne (hn 116 (by decide)),
    Function.update_of_ne (hn 102 (by decide)),
    Function.update_of_ne (hn 81 (by decide)),
    Function.update_of_ne (hn 74 (by decide)),
    Function.update_of_ne (hn 73 (by decide)),
    Function.update_of_ne (hn 66 (by decide)),
    Function.update_of_ne (hn 101 (by decide)),
    Function.update_of_ne (hn 100 (by decide)),
    Function.update_of_ne (hn 78 (by decide)),
    SubexpNodeWorkspace.initial_master masters i hi]

theorem originReady {masters : Store} {node cache index modulus targetWidth sourceWidth : List Bool}
    {d : Data} (H : OriginMasters masters modulus targetWidth sourceWidth)
    (hs : d.stacks = indexed masters node cache index) :
    SubexpNodeOriginReady.Ready d modulus targetWidth sourceWidth cache := by
  constructor
  · rw [hs, indexed_master masters node cache index 128 (by decide)]
    exact H.modulus
  · rw [hs]
    simp only [indexed, Function.update_of_ne (by decide : (74 : Fin 288) ≠ 116),
      cached, Function.update_of_ne (by decide : (74 : Fin 288) ≠ 102),
      Function.update_of_ne (by decide : (74 : Fin 288) ≠ 81), Function.update_self]
    exact H.targetWidth
  · rw [hs, indexed_master masters node cache index 129 (by decide)]
    exact H.sourceWidth
  · simp only [hs, indexed, cached, Function.update_of_ne (by decide : (102 : Fin 288) ≠ 116),
      Function.update_self]
  · intro i hlo hhi
    rw [hs]
    exact SubexpNodeBasisWorkspace.indexed_work masters node cache index i hlo (by omega)
  · rw [hs]
    exact SubexpNodeBasisWorkspace.indexed_work masters node cache index 227 (by decide) (by decide)

theorem packetStatics {masters : Store} {node cache index : List Bool}
    {scopes : List (List ℕ)} {tables : List (List Bool)} {lagrange : List (List (List Bool))}
    {zero one : List Bool} {d : Data}
    (H : PacketMasters masters scopes tables lagrange zero one)
    (hs : d.stacks = indexed masters node cache index) :
    SubexpNodePacketReady.Statics d scopes tables lagrange zero one := by
  constructor
  · rw [hs, indexed_master masters node cache index 256 (by decide)]
    exact H.scopes
  · rw [hs, indexed_master masters node cache index 257 (by decide)]
    exact H.tables
  · rw [hs, indexed_master masters node cache index 284 (by decide)]
    exact H.lagrange
  · rw [hs, indexed_master masters node cache index 119 (by decide)]
    exact H.zero
  · rw [hs, indexed_master masters node cache index 120 (by decide)]
    exact H.one
  · rw [hs]
    exact SubexpNodeBasisWorkspace.indexed_work masters node cache index 224 (by decide) (by decide)
  · rw [hs]
    exact SubexpNodeBasisWorkspace.indexed_work masters node cache index 225 (by decide) (by decide)

theorem finished_empty (masters : Store) (node cache index banks origins : List Bool)
    (i : Fin 288) (hlo : 138 ≤ i.val) (hhi : i.val < 255)
    (h204 : i ≠ 204) (h227 : i ≠ 227) :
    finishedStacks (indexed masters node cache index) banks origins i = [] := by
  simp only [finishedStacks, Function.update_of_ne h227, Function.update_of_ne h204]
  by_cases h201 : i = 201
  · subst i; exact Function.update_self _ _ _
  · rw [Function.update_of_ne h201]
    exact SubexpNodeBasisWorkspace.indexed_work masters node cache index i hlo hhi

/-- The real first-three-call result supplies the complete raw-template
workspace, including the cleared matrix input201 and untouched output15. -/
theorem raw_ready (masters : Store) (node cache index banks origins : List Bool) :
    SubexpRawTemplate.Ready (finishedStacks (indexed masters node cache index) banks origins) := by
  have hz := finished_empty masters node cache index banks origins
  have hc : SubexpRawTemplate.ColorWork
      (finishedStacks (indexed masters node cache index) banks origins) := by
    constructor
    · intro i hlo hhi
      have h204 : i ≠ 204 := by intro he; subst i; change 204 ≤ 201 at hhi; omega
      have h227 : i ≠ 227 := by intro he; subst i; change 227 ≤ 201 at hhi; omega
      exact hz i hlo (by omega) h204 h227
    all_goals exact hz _ (by decide) (by decide) (by decide) (by decide)
  exact { toColorWork := hc
          bases := hz 205 (by decide) (by decide) (by decide) (by decide)
          outsideMaster := hz 208 (by decide) (by decide) (by decide) (by decide)
          groupRecords := hz 211 (by decide) (by decide) (by decide) (by decide)
          groups := hz 212 (by decide) (by decide) (by decide) (by decide)
          block := hz 217 (by decide) (by decide) (by decide) (by decide)
          color := hz 219 (by decide) (by decide) (by decide) (by decide)
          blocks := hz 221 (by decide) (by decide) (by decide) (by decide)
          output := rfl }

theorem raw_ready_of_stacks {masters : Store} {node cache index banks origins : List Bool}
    {d : Data}
    (hs : d.stacks = finishedStacks (indexed masters node cache index) banks origins) :
    SubexpRawTemplate.Ready d.stacks := by
  rw [hs]
  exact raw_ready masters node cache index banks origins

/-- Packet generation changes only its output225 and consumed origin227;
neither port is scratch required by raw-template execution. -/
theorem raw_ready_after_packets {s : Store} (h : SubexpRawTemplate.Ready s)
    (packets : List Bool) :
    SubexpRawTemplate.Ready (Function.update (Function.update s 227 []) 225 packets) := by
  have hc : SubexpRawTemplate.ColorWork (Function.update (Function.update s 227 []) 225 packets) := by
    constructor
    · intro i hlo hhi
      have h225 : i ≠ 225 := by intro he; subst i; change 225 ≤ 201 at hhi; omega
      have h227 : i ≠ 227 := by intro he; subst i; change 227 ≤ 201 at hhi; omega
      simpa only [Function.update_of_ne h225, Function.update_of_ne h227] using h.workspace i hlo hhi
    · simpa using h.bank
    · simpa using h.payload
    · simpa using h.support
    · simpa using h.factors
    · simpa using h.term
    · simpa using h.terms
    · simpa using h.group
    · simpa using h.scratch
    · simpa using h.outside
    · simpa using h.forward
  exact { toColorWork := hc
          bases := by simpa using h.bases
          outsideMaster := by simpa using h.outsideMaster
          groupRecords := by simpa using h.groupRecords
          groups := by simpa using h.groups
          block := by simpa using h.block
          color := by simpa using h.color
          blocks := by simpa using h.blocks
          output := by simpa using h.output }

end SubexponentialSAT.SubexpNodeBlueprintWorkspace

end OAI.Algorithms
