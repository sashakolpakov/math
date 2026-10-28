import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRawTemplateSelectors

namespace OAI.Algorithms

/-! Actual input invariants and measured costs for one color group. -/

namespace SubexponentialSAT.SubexpRawTemplate

open BitProgram StructuredCalls SubexpScanPrimitives
open Subexp.ConstructivePacking

attribute [local simp] Fin.coe_ofNat_eq_mod

variable {D r Q Δ : ℕ}

structure Masters
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (items : List (SubexpFactorRoutingTraversal.Item r Q))
    (suffix : Word) (store : Store) : Prop where
  assignment : store 258 = SubexpFactorRoutingTraversal.words items ++ suffix
  packets : store 225 = Encoding.encodeList id (items.map Prod.snd)
  node : store 116 = List.replicate t.val true
  colors : store 261 = List.replicate r true
  width : (store 260).length = Q * r
  dimension : store 109 = List.replicate D true
  metadata : store 269 = Subexp.SupportSelectionProgram.metadataTable P

/-- These cells carry actual immutable inputs to each selector call. -/
def masterPorts : List (Fin 288) := [109, 116, 225, 258, 260, 261, 269]

theorem Masters.of_frame
    {P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ)}
    {t : Fin Q} {items : List (SubexpFactorRoutingTraversal.Item r Q)}
    {suffix : Word} {a b : Store} (h : Masters P t items suffix a)
    (hf : ∀ i ∈ masterPorts, b i = a i) : Masters P t items suffix b := by
  constructor
  · exact (hf 258 (by decide)).trans h.assignment
  · exact (hf 225 (by decide)).trans h.packets
  · exact (hf 116 (by decide)).trans h.node
  · exact (hf 261 (by decide)).trans h.colors
  · simpa only [hf 260 (by decide)] using h.width
  · exact (hf 109 (by decide)).trans h.dimension
  · exact (hf 269 (by decide)).trans h.metadata

structure ColorWork (store : Store) : Prop where
  workspace : ∀ i : Fin 288, 138 ≤ i.val → i.val ≤ 201 → store i = []
  bank : store 206 = []
  payload : store 207 = []
  support : store 209 = []
  factors : store 210 = []
  term : store 213 = []
  terms : store 215 = []
  group : store 216 = []
  scratch : store 218 = []
  outside : store 223 = []
  forward : store 224 = []

/-- The value is the already proved cost of the actual router, written
using the known input bytes so it does not depend on irrelevant storage. -/
def factorCost (t : Fin Q) (g : Fin r)
    (items : List (SubexpFactorRoutingTraversal.Item r Q))
    (suffix bits : Word) : ℕ :=
  ((7 * (SubexpFactorRoutingTraversal.words items ++ suffix).length + 5) +
    (7 * (Encoding.encodeList id (items.map Prod.snd)).length + 5) +
    (7 * bits.length + 5) + CounterConversions.runtimeBound bits +
    (7 * t.val + 5) + 4) +
  (2 + SubexpFactorRoutingTraversal.budget (Q * r) t.val r g.val items) +
  (10 * (Encoding.encodeList id (SubexpFactorRoutingTraversal.retained t g items).reverse).length +
    2 * suffix.length + 2 * g.val + 2 * t.val + 25) + 1

theorem factorCost_eq
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (g : Fin r) (items : List (SubexpFactorRoutingTraversal.Item r Q))
    (suffix bits : Word) (d : Data) (hm : Masters P t items suffix d.stacks)
    (hbits : d.stacks 219 = bits) :
    SubexpFactorRouting.runtime (projectState id factorPort d) t g items suffix =
      factorCost t g items suffix bits := by
  simp [SubexpFactorRouting.runtime, SubexpFactorRoutingSetup.prepareBudget,
    projectState, factorPort, hm.assignment, hm.packets, hm.node, hbits, factorCost]

def colorGroupBytes
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (items : List (SubexpFactorRoutingTraversal.Item r Q))
    (g : Fin r) (increments : List Word) : Word :=
  groupBytes (selectedSupport P t g.val) (routedBytes t g items) increments

def groupStepCost
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (items : List (SubexpFactorRoutingTraversal.Item r Q))
    (suffix : Word) (g : Fin r) (increments : List Word) : ℕ :=
  9 * (Encoding.encodeList id increments).length + 7 +
  factorCost t g items suffix (colorWord g.val) +
  Subexp.SupportSelectionProgram.budget
    (Subexp.SupportSelectionProgram.metadataTable P).length D t.val r (colorWord g.val) +
  (2 * (selectedOutside P).length + 3) +
  groupCost (selectedSupport P t g.val) (routedBytes t g items) increments +
  (8 * (colorGroupBytes P t items g increments).length + 9) +
  (2 * (colorGroupBytes P t items g increments).length + 3) +
  (2 * (selectedSupport P t g.val).length + 3) +
  (2 * (routedBytes t g items).length + 3) +
  (CounterPrograms.rippleCost true (colorWord g.val) + 1)

/-- The only persistent changes of a color iteration. -/
def colorStore
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (items : List (SubexpFactorRoutingTraversal.Item r Q))
    (g : Fin r) (increments : List Word) (store : Store) : Store :=
  Function.update
    (Function.update store 211
      ((record (colorGroupBytes P t items g increments)).reverse ++ store 211))
    219 (colorWord (g.val + 1))

theorem colorStore_masters
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (items : List (SubexpFactorRoutingTraversal.Item r Q))
    (suffix : Word) (g : Fin r) (increments : List Word) (store : Store)
    (hm : Masters P t items suffix store) :
    Masters P t items suffix (colorStore P t items g increments store) := by
  apply hm.of_frame
  intro i hi
  simp only [masterPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [colorStore]

theorem colorStore_work
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (items : List (SubexpFactorRoutingTraversal.Item r Q))
    (g : Fin r) (increments : List Word) (store : Store) (hw : ColorWork store) :
    ColorWork (colorStore P t items g increments store) := by
  constructor
  · intro i hlo hhi
    have h211 : i ≠ 211 := by intro h; subst i; norm_num at hhi
    have h219 : i ≠ 219 := by intro h; subst i; norm_num at hhi
    simpa [colorStore, h211, h219] using hw.workspace i hlo hhi
  · simpa [colorStore] using hw.bank
  · simpa [colorStore] using hw.payload
  · simpa [colorStore] using hw.support
  · simpa [colorStore] using hw.factors
  · simpa [colorStore] using hw.term
  · simpa [colorStore] using hw.terms
  · simpa [colorStore] using hw.group
  · simpa [colorStore] using hw.scratch
  · simpa [colorStore] using hw.outside
  · simpa [colorStore] using hw.forward

end SubexponentialSAT.SubexpRawTemplate

end OAI.Algorithms
