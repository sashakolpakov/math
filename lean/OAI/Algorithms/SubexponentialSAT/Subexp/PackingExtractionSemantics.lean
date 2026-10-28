import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingExtractionOuter
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingMetadata
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingAddressSemantics

namespace OAI.Algorithms

/-! The records emitted by block extraction have the exact computed packing order. -/

namespace SubexponentialSAT.Subexp.PackingExtraction

open ConstructivePacking MatrixProgramSupport

def blockRows (i : ℕ) (entries : List Entry) (block : List Bool) :
    List (List Bool × List Bool) :=
  entries.map fun e => (entryVertex i e, PackingEntryEmitter.metadataPayload block e.1)

def vertexPrefix (vertices : List (List Bool)) : List Bool :=
  vertices.flatMap fun v => true :: Encoding.frame v

theorem emitEntries_metadata (i : ℕ) (entries : List Entry) (c : Context) :
    (emitEntries i entries c).metadata =
      SelectorProgram.rawRecords (blockRows i entries c.block).reverse ++ c.metadata := by
  induction entries generalizing c with
  | nil => simp [emitEntries, blockRows, SelectorProgram.rawRecords]
  | cons e es ih =>
    change (emitEntries i es (emitted c e.1 (entryVertex i e))).metadata = _
    rw [ih]
    simp [blockRows, emitted, PackingEntryEmitter.metadataOutput, SelectorProgram.rawRecords,
      List.reverse_cons, List.flatMap_append, List.append_assoc]

theorem emitEntries_storage (i : ℕ) (entries : List Entry) (c : Context) :
    (emitEntries i entries c).storage =
      (vertexPrefix (entries.map (entryVertex i))).reverse ++ c.storage := by
  induction entries generalizing c with
  | nil => simp [emitEntries, vertexPrefix]
  | cons e es ih =>
    change (emitEntries i es (emitted c e.1 (entryVertex i e))).storage = _
    rw [ih]
    simp [vertexPrefix, emitted, PackingEntryEmitter.storageOutput,
      List.reverse_append, List.append_assoc]

theorem emitEntries_address (i : ℕ) (entries : List Entry) (c : Context) :
    (emitEntries i entries c).address = List.replicate entries.length true ++ c.address := by
  induction entries generalizing c with
  | nil => rfl
  | cons e es ih =>
    change (emitEntries i es (emitted c e.1 (entryVertex i e))).address = _
    rw [ih]
    simp only [List.length_cons, List.replicate_add, emitted]
    simp [List.append_assoc]

def coverRows (entries : List Entry) (n start : ℕ) : List (List Bool × List Bool) :=
  (List.range' start n).flatMap fun i => blockRows i entries (PackingMetadata.unary i)

def coverVertices (entries : List Entry) (n start : ℕ) : List (List Bool) :=
  (List.range' start n).flatMap fun i => entries.map (entryVertex i)

theorem advanceMany_metadata (entries : List Entry) (n i : ℕ) (c : Context)
    (hblock : c.block = PackingMetadata.unary i) :
    (advanceMany entries n i c).metadata =
      SelectorProgram.rawRecords (coverRows entries n i).reverse ++ c.metadata := by
  induction n generalizing i c with
  | zero => simp [advanceMany, coverRows, SelectorProgram.rawRecords]
  | succ n ih =>
    have hb : (advanced i entries c).block = PackingMetadata.unary (i + 1) := by
      rw [(advanced_static i entries c).1, hblock]
      simp [PackingMetadata.unary, List.replicate_succ]
    rw [advanceMany, ih _ _ hb]
    have hm : (advanced i entries c).metadata = (emitEntries i entries c).metadata := rfl
    rw [hm, emitEntries_metadata, hblock]
    simp [coverRows, List.range'_succ, List.reverse_append, SelectorProgram.rawRecords,
      List.flatMap_append, List.append_assoc]

theorem advanceMany_storage (entries : List Entry) (n i : ℕ) (c : Context) :
    (advanceMany entries n i c).storage =
      (vertexPrefix (coverVertices entries n i)).reverse ++ c.storage := by
  induction n generalizing i c with
  | zero => simp [advanceMany, coverVertices, vertexPrefix]
  | succ n ih =>
    rw [advanceMany, ih]
    have hs : (advanced i entries c).storage = (emitEntries i entries c).storage := rfl
    rw [hs, emitEntries_storage]
    simp [coverVertices, vertexPrefix, List.range'_succ, List.flatMap_append,
      List.reverse_append, List.append_assoc]

theorem emitEntries_address_unary (i : ℕ) (entries : List Entry) (c : Context) (a : ℕ)
    (ha : c.address = PackingMetadata.unary a) :
    (emitEntries i entries c).address = PackingMetadata.unary (a + entries.length) := by
  rw [emitEntries_address, ha]
  change List.replicate entries.length true ++ List.replicate a true =
    List.replicate (a + entries.length) true
  rw [← List.replicate_add, Nat.add_comm entries.length a]

/-- The address table is prepended in the same order as the storage stream. -/
theorem emitEntries_addresses (i : ℕ) (entries : List Entry) (c : Context) (a : ℕ)
    (ha : c.address = PackingMetadata.unary a) :
    (emitEntries i entries c).addresses =
      SelectorProgram.rawRecords
        (PackingAddressSemantics.addressRows (entries.map (entryVertex i)) a).reverse ++
          c.addresses := by
  induction entries generalizing c a with
  | nil => simp [emitEntries, SelectorProgram.rawRecords]
  | cons e es ih =>
    have hd : (emitted c e.1 (entryVertex i e)).address =
        PackingMetadata.unary (a + 1) := by
      simp [emitted, ha, PackingMetadata.unary, List.replicate_succ]
    change (emitEntries i es (emitted c e.1 (entryVertex i e))).addresses = _
    rw [ih _ _ hd]
    simp [PackingAddressSemantics.addressRows_cons, List.reverse_cons,
      SelectorProgram.rawRecords, List.flatMap_append, emitted,
      PackingEntryEmitter.addressOutput, ha, PackingMetadata.unary, List.append_assoc]

theorem coverVertices_succ (entries : List Entry) (n i : ℕ) :
    coverVertices entries (n + 1) i =
      entries.map (entryVertex i) ++ coverVertices entries n (i + 1) := by
  simp [coverVertices, List.range'_succ]

theorem advanceMany_addresses (entries : List Entry) (n i : ℕ) (c : Context) (a : ℕ)
    (ha : c.address = PackingMetadata.unary a) :
    (advanceMany entries n i c).addresses =
      SelectorProgram.rawRecords
        (PackingAddressSemantics.addressRows (coverVertices entries n i) a).reverse ++
          c.addresses := by
  induction n generalizing i c a with
  | zero => simp [advanceMany, coverVertices, SelectorProgram.rawRecords]
  | succ n ih =>
    have hd : (advanced i entries c).address =
        PackingMetadata.unary (a + entries.length) :=
      emitEntries_address_unary i entries c a ha
    rw [advanceMany, ih _ _ _ hd]
    have hs : (advanced i entries c).addresses = (emitEntries i entries c).addresses := rfl
    rw [hs, emitEntries_addresses i entries c a ha, coverVertices_succ]
    simp [PackingAddressSemantics.addressRows_append, List.reverse_append,
      SelectorProgram.rawRecords, List.flatMap_append, List.append_assoc]

theorem advanceMany_address_unary (entries : List Entry) (n i : ℕ) (c : Context) (a : ℕ)
    (ha : c.address = PackingMetadata.unary a) :
    (advanceMany entries n i c).address = PackingMetadata.unary (a + n * entries.length) := by
  induction n generalizing i c a with
  | zero => simpa [advanceMany] using ha
  | succ n ih =>
    have hd : (advanced i entries c).address = PackingMetadata.unary (a + entries.length) :=
      emitEntries_address_unary i entries c a ha
    rw [advanceMany, ih _ _ _ hd]
    congr 1
    ring

theorem advanceMany_static (entries : List Entry) (n i : ℕ) (c : Context)
    (hb : c.block = PackingMetadata.unary i)
    (hr : c.remaining = PackingMetadata.unary n) :
    (advanceMany entries n i c).block = PackingMetadata.unary (i + n) ∧
    (advanceMany entries n i c).remaining = [] ∧
    (advanceMany entries n i c).buckets = c.buckets := by
  induction n generalizing i c with
  | zero =>
    simpa only [advanceMany, Nat.add_zero, PackingMetadata.unary,
      List.replicate_zero] using
      And.intro hb (And.intro hr (rfl : c.buckets = c.buckets))
  | succ n ih =>
    obtain ⟨hb', ht', hr'⟩ := advanced_static i entries c
    have hb'' : (advanced i entries c).block = PackingMetadata.unary (i + 1) := by
      rw [hb', hb]
      simp [PackingMetadata.unary, List.replicate_succ]
    have hr'' : (advanced i entries c).remaining = PackingMetadata.unary n := by
      rw [hr', hr]
      simp [PackingMetadata.unary, List.replicate_succ]
    obtain ⟨hblock, hremaining, hbuckets⟩ := ih (i + 1) (advanced i entries c) hb'' hr''
    refine ⟨?_, hremaining, hbuckets.trans ht'⟩
    simpa only [advanceMany, Nat.add_assoc, Nat.add_comm 1 n] using hblock

variable {V U : Type*} [DecidableEq V] [DecidableEq U]

def typedEntries (P : PackingData V U) (encodeVertex : V → List Bool)
    (encodeType : U → List Bool) : List Entry :=
  P.types.values.map fun u => (encodeType u, (P.bucket u).map encodeVertex)

omit [DecidableEq V] in
theorem entryVertex_typed (P : PackingData V U) (encodeVertex : V → List Bool)
    (encodeType : U → List Bool) (i : Fin P.blockCount) (u : U) :
    entryVertex i.val (encodeType u, (P.bucket u).map encodeVertex) =
      encodeVertex (P.vertexAt i u) := by
  have hi : i.val < (P.bucket u).length := i.isLt.trans_le (P.blockCount_le_bucket u)
  rw [entryVertex, List.getD_eq_getElem _ [] (by simpa using hi)]
  simp [PackingData.vertexAt]

omit [DecidableEq V] in
theorem typedEntries_valid (P : PackingData V U) (encodeVertex : V → List Bool)
    (encodeType : U → List Bool) :
    ∀ e ∈ typedEntries P encodeVertex encodeType, P.blockCount ≤ e.2.length := by
  intro e he
  obtain ⟨u, _, rfl⟩ := List.mem_map.mp he
  simpa using P.blockCount_le_bucket u

theorem coverRows_typed (P : PackingData V U) (encodeVertex : V → List Bool)
    (encodeType : U → List Bool) :
    coverRows (typedEntries P encodeVertex encodeType) P.blockCount 0 =
      (PackingReorder.packedVertices P).map (PackingMetadata.row P encodeVertex encodeType) := by
  unfold coverRows
  rw [← List.range_eq_range', ← List.map_coe_finRange]
  simp only [List.flatMap_map, blockRows, typedEntries, List.map_map,
    PackingReorder.packedVertices, List.map_flatMap]
  apply congrArg (fun f => (List.finRange P.blockCount).flatMap f)
  funext i
  apply List.map_congr_left
  intro u _
  simp only [Function.comp_apply]
  rw [entryVertex_typed]
  simp [PackingMetadata.row, PackingEntryEmitter.metadataPayload,
    GlobalBasisMetadata.Metadata.encode]

omit [DecidableEq V] in
theorem coverVertices_typed (P : PackingData V U) (encodeVertex : V → List Bool)
    (encodeType : U → List Bool) :
    coverVertices (typedEntries P encodeVertex encodeType) P.blockCount 0 =
      (PackingReorder.packedVertices P).map encodeVertex := by
  unfold coverVertices
  rw [← List.range_eq_range', ← List.map_coe_finRange]
  simp only [List.flatMap_map, typedEntries, List.map_map,
    PackingReorder.packedVertices, List.map_flatMap]
  apply congrArg (fun f => (List.finRange P.blockCount).flatMap f)
  funext i
  apply List.map_congr_left
  intro u _
  exact entryVertex_typed P encodeVertex encodeType i u

/-- The covered metadata bytes returned by the actual extraction trace. -/
theorem typed_extraction_metadata (P : PackingData V U) (encodeVertex : V → List Bool)
    (encodeType : U → List Bool) (c : Context) (hblock : c.block = []) :
    (advanceMany (typedEntries P encodeVertex encodeType) P.blockCount 0 c).metadata =
      SelectorProgram.rawRecords (PackingMetadata.coveredRecords P encodeVertex encodeType) ++
        c.metadata := by
  rw [advanceMany_metadata _ _ _ _ (by simpa [PackingMetadata.unary] using hblock), coverRows_typed]
  simp [PackingMetadata.coveredRecords, List.map_reverse]

omit [DecidableEq V] in
theorem typed_extraction_storage (P : PackingData V U) (encodeVertex : V → List Bool)
    (encodeType : U → List Bool) (c : Context) :
    (advanceMany (typedEntries P encodeVertex encodeType) P.blockCount 0 c).storage =
      (vertexPrefix ((PackingReorder.packedVertices P).map encodeVertex)).reverse ++ c.storage := by
  rw [advanceMany_storage, coverVertices_typed]

omit [DecidableEq V] in
/-- Exact address bytes emitted by complete-block extraction, retaining the
initial table and allowing a nonzero initial storage address. -/
theorem typed_extraction_addresses (P : PackingData V U) (encodeVertex : V → List Bool)
    (encodeType : U → List Bool) (c : Context) (a : ℕ)
    (ha : c.address = PackingMetadata.unary a) :
    (advanceMany (typedEntries P encodeVertex encodeType) P.blockCount 0 c).addresses =
      SelectorProgram.rawRecords
        (PackingAddressSemantics.addressRows
          ((PackingReorder.packedVertices P).map encodeVertex) a).reverse ++ c.addresses := by
  rw [advanceMany_addresses _ _ _ _ a ha, coverVertices_typed]

end SubexponentialSAT.Subexp.PackingExtraction

end OAI.Algorithms
