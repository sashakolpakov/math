import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRawTemplateExecution
import OAI.Algorithms.SubexponentialSAT.SubexpTemplateSourceData
import OAI.Algorithms.SubexponentialSAT.Subexp.SupportSelectionSemantics
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockCoefficientContext

namespace OAI.Algorithms

/-!
# Ordered raw templates from the actual banks and factor packets

The physical producer filters the original factor list by its assigned
word, visits colors in ascending order, and retains every bank list's
order. These constructors give its bytes the typed template interpretation
used by the source proof. They do not supply an execution or cost premise.
-/

namespace SubexponentialSAT.Subexp.RawTemplateRefinement

open MulticolorTypes ConstructivePacking SupportSelectionProgram
open SubexpTemplatePointServices

variable {p D r Q Δ : ℕ} [Fact p.Prime]

def scalarWords (v : Fin D → ZMod p) : Fin D → BaseWord p :=
  fun i => ⟨MatrixWordEncoding.word p (v i), MatrixWordEncoding.word_length p (v i)⟩

def vectorBytes (v : Fin D → ZMod p) : List Bool :=
  (BlockCoefficientProgram.vectorWords p v).flatten

omit [Fact p.Prime] in
theorem scalarWords_bytes (v : Fin D → ZMod p) :
    SubexpTemplateData.bankBytes (scalarWords v) = vectorBytes v := by
  simp only [SubexpTemplateData.bankBytes, DensePolynomialLoop.flatten, scalarWords,
    vectorBytes, BlockCoefficientProgram.vectorWords, List.ofFn_eq_map,
    List.map_map, Function.comp_def]

theorem scalarWords_value (v : Fin D → ZMod p) (i : Fin D) :
    SubexpWordLift.sourceValue p (scalarWords v i) = v i :=
  MatrixWordEncoding.word_field_value p (v i)

theorem scalarWords_canonical (v : Fin D → ZMod p) (i : Fin D) :
    BinaryArithmetic.toNat (scalarWords v i).val < p :=
  MatrixWordEncoding.word_canonical p (v i)

variable (P : PackingData (Fin D) (UniversalType r Q Δ)) (t : Fin Q)

def colorSupport (g : Fin r) : List (Fin D) :=
  (List.finRange D).filter (colorAt P t g.val)

def outsideSupport : List (Fin D) :=
  (List.finRange D).filter (outsideAt P)

theorem colorSupport_nodup (g : Fin r) : (colorSupport P t g).Nodup :=
  (List.nodup_finRange D).filter _

theorem outsideSupport_nodup : (outsideSupport P).Nodup :=
  (List.nodup_finRange D).filter _

theorem mem_colorSupport (g : Fin r) (v : Fin D) :
    v ∈ colorSupport P t g ↔
      v ∈ DirectSums.packedSupportFinset P.completeBlocks.embed (side (Δ := Δ) t g).toFinset := by
  simp only [colorSupport, List.mem_filter, List.mem_finRange, true_and]
  exact SupportSelectionSemantics.colorAt_true_iff P t g v

theorem mem_outsideSupport (v : Fin D) :
    v ∈ outsideSupport P ↔ v ∉ Set.range P.completeBlocks.embed := by
  simp only [outsideSupport, List.mem_filter, List.mem_finRange, true_and]
  exact SupportSelectionSemantics.outsideAt_true_iff P v

theorem selectedSupport_eq (g : Fin r) :
    SubexpRawTemplate.selectedSupport P t g.val =
      SubexpTemplateData.supportBytes (colorSupport P t g) := by
  rw [SubexpRawTemplate.selectedSupport, SupportSelectionSemantics.color_indexWords P t g]
  rfl

theorem selectedOutside_eq :
    SubexpRawTemplate.selectedOutside P = SubexpTemplateData.supportBytes (outsideSupport P) := by
  have hfilter : (List.range D).filter (outsideTest P) =
      ((List.finRange D).filter (outsideAt P)).map Fin.val := by
    rw [← List.map_coe_finRange D, List.filter_map]
    simp only [Function.comp_def, outsideTest, Fin.isLt, dite_true]
  simp only [SubexpRawTemplate.selectedOutside, indexWords, hfilter, List.map_map,
    SubexpTemplateData.supportBytes, SubexpWeightGather.supportBits, outsideSupport,
    Function.comp_def]

variable {F : Type*} (factors : List F) (words : F → Word r Q)
variable (packets : F → SubexpTemplateFactors.Factor p D)

/-- Original factor order is retained even when packet payloads coincide. -/
def items : List (SubexpFactorRoutingTraversal.Item r Q) :=
  factors.map fun e => (words e, SubexpTemplateFactors.encode (packets e))

def colorFactors (g : Fin r) : List (SubexpTemplateFactors.Factor p D) :=
  (factors.filter fun e => decide (words e t = g)).map packets

omit [Fact p.Prime] in
theorem routedBytes_eq (g : Fin r) :
    SubexpRawTemplate.routedBytes t g (items factors words packets) =
      Encoding.encodeList SubexpTemplateFactors.encode (colorFactors t factors words packets g) := by
  simp only [SubexpRawTemplate.routedBytes, SubexpFactorRoutingTraversal.retained,
    items, List.filter_map, List.map_map, Function.comp_def, colorFactors,
    SubexpBlueprintRows.encodeList_map] ; rfl

def term (g : Fin r) (increment : Fin D → ZMod p) : SubexpTemplateData.Term p D where
  increment := scalarWords increment
  support := colorSupport P t g
  factors := colorFactors t factors words packets g

def group (g : Fin r) (increments : List (Fin D → ZMod p)) :
    List (SubexpTemplateData.Term p D) :=
  increments.map (term P t factors words packets g)

def block (increments : Fin r → List (Fin D → ZMod p))
    (base : Fin D → ZMod p) : SubexpTemplateData.Block p D where
  base := scalarWords base
  support := outsideSupport P
  groups := List.ofFn fun g => group P t factors words packets g (increments g)

def blocks (bases : List (Fin D → ZMod p)) (increments : Fin r → List (Fin D → ZMod p)) :
    List (SubexpTemplateData.Block p D) :=
  bases.map (block P t factors words packets increments)

omit [Fact p.Prime] in
theorem term_bytes (g : Fin r) (increment : Fin D → ZMod p) :
    SubexpRawTemplate.termBytes (vectorBytes increment)
        (SubexpRawTemplate.selectedSupport P t g.val)
        (SubexpRawTemplate.routedBytes t g (items factors words packets)) =
      SubexpTemplateProgram.encodeTerm
        (SubexpTemplateData.rawTerm (term P t factors words packets g increment)) := by
  rw [selectedSupport_eq P t g, routedBytes_eq t factors words packets g]
  simp only [SubexpRawTemplate.termBytes, SubexpTemplateProgram.encodeTerm,
    SubexpTemplateData.rawTerm, term, scalarWords_bytes,
    SubexpBlueprintRows.encodeList_map] ; rfl

omit [Fact p.Prime] in
theorem group_bytes (g : Fin r) (increments : List (Fin D → ZMod p)) :
    SubexpRawTemplate.colorGroupBytes P t (items factors words packets) g
        (increments.map vectorBytes) =
      SubexpTemplateProgram.encodeGroup
        ((group P t factors words packets g increments).map SubexpTemplateData.rawTerm) := by
  simp only [SubexpRawTemplate.colorGroupBytes, SubexpRawTemplate.groupBytes,
    SubexpTemplateProgram.encodeGroup, group, List.map_map,
    SubexpBlueprintRows.encodeList_map, Function.comp_def]
  exact congrArg (fun f => Encoding.encodeList f increments)
    (funext (term_bytes P t factors words packets g))

omit [Fact p.Prime] in
private theorem groupsFrom_ofFn (start n : ℕ) (h : start + n ≤ r)
    (increments : Fin n → List (List Bool)) :
    SubexpRawTemplate.groupsFrom P t (items factors words packets) start (List.ofFn increments) =
      List.ofFn (fun j : Fin n => SubexpRawTemplate.colorGroupBytes P t
        (items factors words packets)
        ⟨start + j.val, (Nat.add_lt_add_left j.isLt start).trans_le h⟩ (increments j)) := by
  induction n generalizing start with
  | zero => simp [SubexpRawTemplate.groupsFrom]
  | succ n ih =>
    have hs : start < r := by omega
    rw [List.ofFn_succ, SubexpRawTemplate.groupsFrom, dite_eq_left hs, List.ofFn_succ]
    apply congrArg₂ List.cons
    · simp only [Fin.val_zero, Nat.add_zero]
    · rw [ih (start + 1) (by omega)]
      apply congrArg List.ofFn
      funext j
      congr 1
      apply Fin.ext
      simp only [Fin.val_succ]
      omega

omit [Fact p.Prime] in
theorem groupsFrom_family (increments : Fin r → List (List Bool)) :
    SubexpRawTemplate.groupsFrom P t (items factors words packets) 0 (List.ofFn increments) =
      List.ofFn (fun g => SubexpRawTemplate.colorGroupBytes P t
        (items factors words packets) g (increments g)) := by
  simpa only [Nat.zero_add] using
    groupsFrom_ofFn P t factors words packets 0 r (by omega) increments

omit [Fact p.Prime] in
theorem groups_bytes (increments : Fin r → List (Fin D → ZMod p)) :
    SubexpRawTemplate.groupsFrom P t (items factors words packets) 0
        (List.ofFn fun g => (increments g).map vectorBytes) =
      (List.ofFn fun g => group P t factors words packets g (increments g)).map
        (fun ts => SubexpTemplateProgram.encodeGroup (ts.map SubexpTemplateData.rawTerm)) := by
  rw [groupsFrom_family P t factors words packets, List.map_ofFn]
  apply congrArg List.ofFn
  funext g
  exact group_bytes P t factors words packets g (increments g)

omit [Fact p.Prime] in
theorem outputBytes_eq (bases : List (Fin D → ZMod p))
    (increments : Fin r → List (Fin D → ZMod p)) :
    SubexpRawTemplate.outputBytes P t (items factors words packets)
        (bases.map vectorBytes) (List.ofFn fun g => (increments g).map vectorBytes) =
      SubexpTemplateProgram.encodeBlocks
        ((blocks P t factors words packets bases increments).map SubexpTemplateData.rawBlock) := by
  rw [SubexpRawTemplate.outputBytes, groups_bytes P t factors words packets increments,
    selectedOutside_eq P]
  simp only [SubexpRawTemplate.blocksBytes, blocks, List.map_map,
    SubexpTemplateProgram.encodeBlocks, SubexpBlueprintRows.encodeList_map,
    Function.comp_def]
  apply congrArg (fun f => Encoding.encodeList f bases)
  funext base
  simp only [SubexpRawTemplate.blockBytes, SubexpTemplateProgram.encodeBlock,
    SubexpTemplateData.rawBlock, block, scalarWords_bytes,
    SubexpBlueprintRows.encodeList_map] ; rfl

omit [Fact p.Prime] in
theorem block_good (increments : Fin r → List (Fin D → ZMod p))
    (base : Fin D → ZMod p) :
    SubexpTemplateSourceData.BlockGood (block P t factors words packets increments base) := by
  constructor
  · exact outsideSupport_nodup P
  · intro ts hts s hs
    obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hts
    obtain ⟨increment, _, rfl⟩ := List.mem_map.mp hs
    exact colorSupport_nodup P t g

omit [Fact p.Prime] in
theorem blocks_good (bases : List (Fin D → ZMod p))
    (increments : Fin r → List (Fin D → ZMod p)) :
    ∀ b ∈ blocks P t factors words packets bases increments,
      SubexpTemplateSourceData.BlockGood b := by
  intro b hb
  obtain ⟨base, _, rfl⟩ := List.mem_map.mp hb
  exact block_good P t factors words packets increments base

section Enumeration

variable {k : ℕ} {τ : ℚ} {E : Type*} [Fintype F] [Field E] [Algebra (ZMod p) E]
variable {pattern : Factor.Pattern (Fin D) F}
variable {c : SubexpLayoutSpec.Parameters p k Δ r τ}

/-- Use the enumeration's actual index order directly for every base and
own-color increment. The computed global enumeration supplies this data. -/
def blocksOfEnumeration (L : SubexpLayoutSpec.Layout (E := E) pattern c)
    (node : Fin c.Q) (packing : PackingData (Fin D) (UniversalType r c.Q Δ))
    (data : SubexpLayoutSpec.EnumerationData L node)
    (factorOrder : List F) (word : F → Word r c.Q)
    (packet : F → SubexpTemplateFactors.Factor p D) : List (SubexpTemplateData.Block p D) :=
  blocks packing node factorOrder word packet (List.ofFn data.outerBase)
    (fun g => List.ofFn fun i => (data.incrementEquiv g i).val)

theorem enumeration_outputBytes_eq (L : SubexpLayoutSpec.Layout (E := E) pattern c)
    (node : Fin c.Q) (packing : PackingData (Fin D) (UniversalType r c.Q Δ))
    (data : SubexpLayoutSpec.EnumerationData L node)
    (factorOrder : List F) (word : F → Word r c.Q)
    (packet : F → SubexpTemplateFactors.Factor p D) :
    SubexpRawTemplate.outputBytes packing node (items factorOrder word packet)
        ((List.ofFn data.outerBase).map vectorBytes)
        (List.ofFn fun g => (List.ofFn fun i => (data.incrementEquiv g i).val).map vectorBytes) =
      SubexpTemplateProgram.encodeBlocks
        ((blocksOfEnumeration L node packing data factorOrder word packet).map
          SubexpTemplateData.rawBlock) :=
  outputBytes_eq packing node factorOrder word packet (List.ofFn data.outerBase)
    (fun g => List.ofFn fun i => (data.incrementEquiv g i).val)

theorem blocksOfEnumeration_good (L : SubexpLayoutSpec.Layout (E := E) pattern c)
    (node : Fin c.Q) (packing : PackingData (Fin D) (UniversalType r c.Q Δ))
    (data : SubexpLayoutSpec.EnumerationData L node)
    (factorOrder : List F) (word : F → Word r c.Q)
    (packet : F → SubexpTemplateFactors.Factor p D) :
    ∀ b ∈ blocksOfEnumeration L node packing data factorOrder word packet,
      SubexpTemplateSourceData.BlockGood b :=
  blocks_good packing node factorOrder word packet (List.ofFn data.outerBase)
    (fun g => List.ofFn fun i => (data.incrementEquiv g i).val)

end Enumeration

end SubexponentialSAT.Subexp.RawTemplateRefinement

end OAI.Algorithms
