import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingExtractionSemantics
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingLeftovers

namespace OAI.Algorithms

/-! The actual leftover scan completes the metadata, storage order, and
address table produced by complete-block extraction. -/

namespace SubexponentialSAT.Subexp.PackingOutputSemantics

open ConstructivePacking

theorem vertexPrefix_append_false (vertices : List (List Bool)) :
    PackingExtraction.vertexPrefix vertices ++ [false] =
      ProgramEncoding.encodeRecords vertices := by
  induction vertices with
  | nil => rfl
  | cons v vertices ih =>
    simpa [PackingExtraction.vertexPrefix, ProgramEncoding.encodeRecords,
      Encoding.encodeList, List.append_assoc] using congrArg (fun rest => true :: (Encoding.frame v ++ rest)) ih

theorem addressRecords_eq_addressRows (vertices : List ℕ) (start : ℕ) :
    PackingLeftovers.addressRecords start vertices =
      PackingAddressSemantics.addressRows (vertices.map PackingLeftovers.unary) start := by
  induction vertices generalizing start with
  | nil => rfl
  | cons v vertices ih =>
    simp only [PackingLeftovers.addressRecords, List.map_cons,
      PackingAddressSemantics.addressRows_cons, ih]

theorem metadataRecords_eq_addressRows (vertices : List ℕ) (start : ℕ) :
    PackingLeftovers.metadataRecords start vertices =
      (PackingAddressSemantics.addressRows (vertices.map PackingLeftovers.unary) start).map
        (fun p => (p.1, PackingLeftoverEmitter.metadataPayload p.2)) := by
  induction vertices generalizing start with
  | nil => rfl
  | cons v vertices ih =>
    simp only [PackingLeftovers.metadataRecords, List.map_cons,
      PackingAddressSemantics.addressRows_cons, ih]

variable {V U : Type*} [DecidableEq V] [DecidableEq U]

def vertexBytes (code : V → ℕ) (v : V) : List Bool := PackingMetadata.unary (code v)

omit [DecidableEq V] in
theorem vertexBytes_injective (code : V → ℕ) (hc : Function.Injective code) :
    Function.Injective (vertexBytes code) := PackingMetadata.unary_injective.comp hc

theorem leftovers_eq (P : PackingData V U) (code : V → ℕ)
    (encodeType : U → List Bool) (hc : Function.Injective code) :
    PackingLeftovers.leftovers
        (PackingMetadata.coveredRecords P (vertexBytes code) encodeType)
        (P.vertices.values.map code) = P.leftovers.map code := by
  unfold PackingLeftovers.leftovers
  rw [List.filter_map]
  apply congrArg (List.map code)
  rw [← PackingMetadata.covered_filter_eq_leftovers P (vertexBytes code) encodeType
    (vertexBytes_injective code hc)]
  apply List.filter_congr
  intro v _
  simp only [Function.comp_def]
  unfold PackingLeftovers.covered
  change Bool.not ((PackingMetadata.coveredRecords P (vertexBytes code) encodeType).lookup
      (vertexBytes code v)).isSome =
    decide ((PackingMetadata.coveredRecords P (vertexBytes code) encodeType).lookup
      (vertexBytes code v) = none)
  cases (PackingMetadata.coveredRecords P (vertexBytes code) encodeType).lookup
    (vertexBytes code v) <;> rfl

theorem metadataRecords_leftovers (P : PackingData V U) (code : V → ℕ)
    (encodeType : U → List Bool) :
    PackingLeftovers.metadataRecords 0 (P.leftovers.map code) =
      P.leftovers.map (PackingMetadata.row P (vertexBytes code) encodeType) := by
  rw [metadataRecords_eq_addressRows]
  rw [List.map_map]
  change (PackingAddressSemantics.addressRows (P.leftovers.map (vertexBytes code)) 0).map _ = _
  rw [PackingAddressSemantics.addressRows_map_graph P.leftovers (vertexBytes code)
    P.leftovers_nodup, List.map_map]
  apply List.map_congr_left
  intro v hv
  have hn : P.lookup v = none := (P.lookup_none_iff v).mpr ((P.mem_leftovers v).mp hv)
  simp [ PackingMetadata.row, PackingMetadata.value, hn,
    PackingLeftoverEmitter.metadataPayload, GlobalBasisMetadata.Metadata.encode,
    PackingMetadata.unary]

/-- Exact state after complete-block extraction from empty accumulators. -/
def packedSnapshot (P : PackingData V U) (code : V → ℕ)
    (encodeType : U → List Bool) : PackingLeftovers.Snapshot :=
  { rank := 0
    address := (PackingReorder.packedVertices P).length
    storage := (PackingExtraction.vertexPrefix
      ((PackingReorder.packedVertices P).map (vertexBytes code))).reverse
    metadata := SelectorProgram.rawRecords
      (PackingMetadata.coveredRecords P (vertexBytes code) encodeType)
    addresses := SelectorProgram.rawRecords
      (PackingAddressSemantics.addressRows
        ((PackingReorder.packedVertices P).map (vertexBytes code)) 0).reverse }

def snapshotOf (c : PackingExtraction.Context) : PackingLeftovers.Snapshot :=
  ⟨0, c.address.length, c.storage, c.metadata, c.addresses⟩

theorem snapshotOf_extraction (P : PackingData V U) (code : V → ℕ)
    (encodeType : U → List Bool) (c : PackingExtraction.Context)
    (hb : c.block = []) (ha : c.address = []) (hs : c.storage = [])
    (hm : c.metadata = []) (ht : c.addresses = []) :
    snapshotOf (PackingExtraction.advanceMany
      (PackingExtraction.typedEntries P (vertexBytes code) encodeType) P.blockCount 0 c) =
      packedSnapshot P code encodeType := by
  have hu : c.address = PackingMetadata.unary 0 := ha
  have hn := PackingExtraction.advanceMany_address_unary
    (PackingExtraction.typedEntries P (vertexBytes code) encodeType) P.blockCount 0 c 0 hu
  have hlen : (PackingExtraction.advanceMany
      (PackingExtraction.typedEntries P (vertexBytes code) encodeType)
      P.blockCount 0 c).address.length = (PackingReorder.packedVertices P).length := by
    rw [hn, PackingReorder.packedVertices_length]
    simp [PackingMetadata.unary, PackingExtraction.typedEntries]
  unfold snapshotOf
  rw [hlen, PackingExtraction.typed_extraction_storage,
    PackingExtraction.typed_extraction_metadata _ _ _ _ hb,
    PackingExtraction.typed_extraction_addresses _ _ _ _ 0 hu]
  simp only [hs, hm, ht, List.append_nil] ; rfl

def finish (P : PackingData V U) (code : V → ℕ) (encodeType : U → List Bool)
    (s : PackingLeftovers.Snapshot) : PackingLeftovers.Snapshot :=
  (P.vertices.values.map code).foldl
    (PackingLeftovers.advance (PackingMetadata.coveredRecords P (vertexBytes code) encodeType)) s

theorem finish_metadata (P : PackingData V U) (code : V → ℕ)
    (encodeType : U → List Bool) (hc : Function.Injective code) :
    (finish P code encodeType (packedSnapshot P code encodeType)).metadata =
      SelectorProgram.rawRecords (PackingMetadata.records P (vertexBytes code) encodeType) := by
  unfold finish
  rw [PackingLeftovers.final_metadata, leftovers_eq P code encodeType hc]
  change SelectorProgram.rawRecords
      (PackingLeftovers.metadataRecords 0 (P.leftovers.map code)).reverse ++
      SelectorProgram.rawRecords
        (PackingMetadata.coveredRecords P (vertexBytes code) encodeType) = _
  rw [metadataRecords_leftovers, ← List.map_reverse, ← PackingLeftovers.rawRecords_append,
    ← PackingMetadata.records_eq_leftovers_append]

theorem finish_storage (P : PackingData V U) (code : V → ℕ)
    (encodeType : U → List Bool) (hc : Function.Injective code) :
    (finish P code encodeType (packedSnapshot P code encodeType)).storage =
      (PackingExtraction.vertexPrefix
        ((PackingReorder.storageVertices P).map (vertexBytes code))).reverse := by
  unfold finish
  rw [PackingLeftovers.final_storage, leftovers_eq P code encodeType hc]
  simp [packedSnapshot, PackingLeftovers.storageRecords, PackingReorder.storageVertices,
    PackingExtraction.vertexPrefix, vertexBytes, PackingMetadata.unary,
    List.flatMap_map, List.flatMap_append, List.reverse_append]

theorem finish_addresses (P : PackingData V U) (code : V → ℕ)
    (encodeType : U → List Bool) (hc : Function.Injective code) :
    (finish P code encodeType (packedSnapshot P code encodeType)).addresses =
      SelectorProgram.rawRecords (PackingAddressSemantics.storageAddresses P (vertexBytes code)) := by
  unfold finish
  rw [PackingLeftovers.final_addresses, leftovers_eq P code encodeType hc,
    addressRecords_eq_addressRows]
  simp only [packedSnapshot, PackingAddressSemantics.storageAddresses,
    PackingReorder.storageVertices, List.map_append,
    PackingAddressSemantics.addressRows_append, List.length_map, Nat.zero_add,
    List.reverse_append, PackingLeftovers.rawRecords_append, List.map_map] ; rfl

/-- The final transfer reverses the accumulated bits and appends the list terminator. -/
theorem finish_storage_bytes (P : PackingData V U) (code : V → ℕ)
    (encodeType : U → List Bool) (hc : Function.Injective code) :
    (finish P code encodeType (packedSnapshot P code encodeType)).storage.reverse ++ [false] =
      ProgramEncoding.encodeRecords ((PackingReorder.storageVertices P).map (vertexBytes code)) := by
  rw [finish_storage P code encodeType hc, List.reverse_reverse, vertexPrefix_append_false]

theorem finish_counters (P : PackingData V U) (code : V → ℕ)
    (encodeType : U → List Bool) (hc : Function.Injective code) :
    (finish P code encodeType (packedSnapshot P code encodeType)).rank = P.leftovers.length ∧
    (finish P code encodeType (packedSnapshot P code encodeType)).address =
      (PackingReorder.storageVertices P).length := by
  have h := PackingLeftovers.final_counters
    (PackingMetadata.coveredRecords P (vertexBytes code) encodeType)
    (P.vertices.values.map code) (packedSnapshot P code encodeType)
  rw [leftovers_eq P code encodeType hc] at h
  simpa only [finish, packedSnapshot, List.length_map, Nat.zero_add,
    PackingReorder.storageVertices, List.length_append] using h

/-- All physical accumulators after extraction and the actual leftover scan. -/
theorem finish_extraction_outputs (P : PackingData V U) (code : V → ℕ)
    (encodeType : U → List Bool) (hc : Function.Injective code)
    (c : PackingExtraction.Context) (hb : c.block = []) (ha : c.address = [])
    (hs : c.storage = []) (hm : c.metadata = []) (ht : c.addresses = []) :
    let s := finish P code encodeType (snapshotOf (PackingExtraction.advanceMany
      (PackingExtraction.typedEntries P (vertexBytes code) encodeType) P.blockCount 0 c))
    s.metadata = SelectorProgram.rawRecords
        (PackingMetadata.records P (vertexBytes code) encodeType) ∧
    s.storage = (PackingExtraction.vertexPrefix
        ((PackingReorder.storageVertices P).map (vertexBytes code))).reverse ∧
    s.addresses = SelectorProgram.rawRecords
        (PackingAddressSemantics.storageAddresses P (vertexBytes code)) ∧
    s.rank = P.leftovers.length ∧ s.address = (PackingReorder.storageVertices P).length := by
  dsimp only
  rw [snapshotOf_extraction P code encodeType c hb ha hs hm ht]
  exact ⟨finish_metadata P code encodeType hc, finish_storage P code encodeType hc,
    finish_addresses P code encodeType hc, finish_counters P code encodeType hc⟩

end SubexponentialSAT.Subexp.PackingOutputSemantics

end OAI.Algorithms
