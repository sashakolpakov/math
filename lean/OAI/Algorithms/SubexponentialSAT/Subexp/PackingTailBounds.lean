import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingExecution

namespace OAI.Algorithms

/-!
# Bounds for the actual packing tail

All sizes below come from the represented input and generated records.
There is no assumed runtime certificate: the cost estimates apply to the
same leftover and inverse budgets used by `PackingExecution.program_trace`.
-/

namespace SubexponentialSAT.Subexp.PackingTailBounds

open ConstructivePacking PackingExecution

variable {U : Type*} [DecidableEq U]

def metadataBound (D T : ℕ) : ℕ := D * (6 * D + 4 * T + 8)
def addressBound (D : ℕ) : ℕ := D * (4 * D + 2)
def wordBound (D : ℕ) : ℕ := 1 + (2 * D + 2) * D

private theorem word_length_le_encoded (words : List (List Bool))
    (word : List Bool) (hw : word ∈ words) :
    word.length ≤ (ProgramEncoding.encodeRecords words).length := by
  induction words with
  | nil => simp at hw
  | cons first rest ih =>
    have hlen : (ProgramEncoding.encodeRecords (first :: rest)).length =
        2 * first.length + 2 + (ProgramEncoding.encodeRecords rest).length := by
      exact Encoding.length_encodeList_cons id first rest
    rcases List.mem_cons.mp hw with rfl | hw
    · omega
    · have ht := ih hw
      omega

/-- Every type occurs in the actual generated type stream. -/
theorem type_word_length_le (s : Spec U) (u : U) :
    (s.encodeType u).length ≤ s.params.typeStream.length := by
  change (s.encodeType u).length ≤ (ProgramEncoding.encodeRecords s.params.typeRows).length
  apply word_length_le_encoded
  rw [s.type_records]
  exact List.mem_map.mpr ⟨u, s.types.complete u, rfl⟩

theorem packed_vertices_length_le (s : Spec U) :
    (PackingReorder.packedVertices s.packing).length ≤ s.params.D := by
  simpa only [Fintype.card_fin] using
    (PackingAddressSemantics.packedVertices_nodup s.packing).length_le_card

theorem storage_vertices_length_le (s : Spec U) :
    (PackingReorder.storageVertices s.packing).length ≤ s.params.D := by
  simpa only [Fintype.card_fin] using
    (PackingAddressSemantics.storageVertices_nodup s.packing).length_le_card

theorem leftovers_length_le (s : Spec U) : s.packing.leftovers.length ≤ s.params.D := by
  simpa only [Fintype.card_fin] using s.packing.leftovers_nodup.length_le_card

private theorem metadata_value_length_le (s : Spec U) (v : Fin s.params.D) :
    (PackingMetadata.value s.packing s.encodeType v).encode.length ≤
      2 * s.params.D + 2 * s.params.typeStream.length + 3 := by
  cases hl : s.packing.lookup v with
  | none =>
    have hi : s.packing.leftovers.idxOf v ≤ s.packing.leftovers.length := List.idxOf_le_length
    have hn := leftovers_length_le s
    simp only [PackingMetadata.value, hl, GlobalBasisMetadata.Metadata.encode,
      List.length_cons, Encoding.length_frame, PackingMetadata.unary, List.length_replicate]
    omega
  | some z =>
    have ht := type_word_length_le s z.2
    have hz := z.1.isLt
    have hb := (s.packing.blockCount_le_bucket z.2).trans (s.packing.bucket_length_le z.2)
    simp only [Spec.packing_vertices, List.length_finRange] at hb
    simp only [PackingMetadata.value, hl, GlobalBasisMetadata.Metadata.encode,
      List.length_cons, List.length_append, Encoding.length_frame,
      PackingMetadata.unary, List.length_replicate]
    omega

private theorem raw_length_le (rows : List (List Bool × List Bool)) (K B : ℕ)
    (hk : ∀ row ∈ rows, row.1.length ≤ K)
    (hb : ∀ row ∈ rows, row.2.length ≤ B) :
    (SelectorProgram.rawRecords rows).length ≤ rows.length * (2 * K + 2 * B + 2) := by
  induction rows with
  | nil => simp [SelectorProgram.rawRecords]
  | cons row rows ih =>
    have hkey := hk row (by simp)
    have hvalue := hb row (by simp)
    have htail := ih (fun x hx => hk x (List.mem_cons_of_mem _ hx))
      (fun x hx => hb x (List.mem_cons_of_mem _ hx))
    simp only [SelectorProgram.rawRecords, List.flatMap_cons, List.length_append,
      Encoding.length_frame, List.length_cons] at htail ⊢
    nlinarith

private theorem metadata_list_length_le (s : Spec U) (vs : List (Fin s.params.D))
    (hn : vs.length ≤ s.params.D) :
    (SelectorProgram.rawRecords (vs.map (PackingMetadata.row s.packing s.encodeVertex s.encodeType))).length ≤
      metadataBound s.params.D s.params.typeStream.length := by
  have h := raw_length_le (vs.map (PackingMetadata.row s.packing s.encodeVertex s.encodeType))
    s.params.D (2 * s.params.D + 2 * s.params.typeStream.length + 3)
    (by
      intro row hr
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hr
      simpa only [PackingMetadata.row, Spec.encodeVertex, List.length_replicate] using
        Nat.le_of_lt v.isLt)
    (by
      intro row hr
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hr
      exact metadata_value_length_le s v)
  simp only [List.length_map] at h
  calc
    _ ≤ vs.length * (2 * s.params.D + 2 *
      (2 * s.params.D + 2 * s.params.typeStream.length + 3) + 2) := h
    _ ≤ s.params.D * (2 * s.params.D + 2 *
      (2 * s.params.D + 2 * s.params.typeStream.length + 3) + 2) :=
      Nat.mul_le_mul_right _ hn
    _ = _ := by unfold metadataBound; ring

theorem covered_length_le (s : Spec U) :
    (SelectorProgram.rawRecords (covered s)).length ≤
      metadataBound s.params.D s.params.typeStream.length := by
  exact metadata_list_length_le s (PackingReorder.packedVertices s.packing).reverse
    (by simpa using packed_vertices_length_le s)

theorem metadata_length_le (s : Spec U) :
    s.metadata.length ≤ metadataBound s.params.D s.params.typeStream.length := by
  exact metadata_list_length_le s (PackingReorder.storageVertices s.packing).reverse
    (by simpa using storage_vertices_length_le s)

private theorem address_list_length_le (s : Spec U) (vs : List (Fin s.params.D))
    (hnd : vs.Nodup) (hn : vs.length ≤ s.params.D) :
    (SelectorProgram.rawRecords (PackingAddressSemantics.addressRows
      (vs.map s.encodeVertex) 0).reverse).length ≤ addressBound s.params.D := by
  rw [PackingAddressSemantics.addressRows_map_graph vs s.encodeVertex hnd, ← List.map_reverse]
  have h := raw_length_le
    (vs.reverse.map (fun v => (s.encodeVertex v, List.replicate (vs.idxOf v) true)))
    s.params.D s.params.D
    (by
      intro row hr
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hr
      simpa only [Spec.encodeVertex, List.length_replicate] using Nat.le_of_lt v.isLt)
    (by
      intro row hr
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hr
      simpa only [List.length_replicate] using (List.idxOf_le_length (a := v) (l := vs)).trans hn)
  simp only [List.length_map, List.length_reverse] at h
  calc
    _ ≤ vs.length * (2 * s.params.D + 2 * s.params.D + 2) := h
    _ ≤ s.params.D * (2 * s.params.D + 2 * s.params.D + 2) := Nat.mul_le_mul_right _ hn
    _ = _ := by unfold addressBound; ring

theorem addresses_length_le (s : Spec U) : s.addresses.length ≤ addressBound s.params.D := by
  exact address_list_length_le s (PackingReorder.storageVertices s.packing)
    (PackingAddressSemantics.storageVertices_nodup s.packing) (storage_vertices_length_le s)

theorem address_records_length_le (s : Spec U) :
    (SelectorProgram.rawRecords (addressRecords s)).length ≤ addressBound s.params.D :=
  addresses_length_le s

private theorem encoded_vertices_length_le (s : Spec U) (vs : List (Fin s.params.D))
    (hn : vs.length ≤ s.params.D) :
    (ProgramEncoding.encodeRecords (vs.map s.encodeVertex)).length ≤ wordBound s.params.D := by
  have h := ProgramEncoding.encodeRecords_length_le (vs.map s.encodeVertex) s.params.D (by
    intro word hw
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hw
    simpa only [Spec.encodeVertex, List.length_replicate] using Nat.le_of_lt v.isLt)
  simp only [List.length_map] at h
  exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hn) 1)

theorem storage_length_le (s : Spec U) : s.storage.length ≤ wordBound s.params.D :=
  encoded_vertices_length_le s (PackingReorder.storageVertices s.packing) (storage_vertices_length_le s)

theorem inverse_length_le (s : Spec U) : s.inverse.length ≤ wordBound s.params.D := by
  have h := ProgramEncoding.encodeRecords_length_le
    ((PackingReorder.readPlan s.packing).map PackingMetadata.unary) s.params.D (by
      intro word hw
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hi
      simpa only [PackingMetadata.unary, List.length_replicate] using
        (List.idxOf_le_length (a := v) (l := PackingReorder.storageVertices s.packing)).trans
          (storage_vertices_length_le s))
  simpa only [Spec.inverse, List.length_map, PackingReorder.readPlan_length, Spec.packing_vertices,
    List.length_finRange, wordBound] using h

theorem queries_length_le (D : ℕ) :
    (ProgramEncoding.encodeRecords (PackingProgram.inverseQueries D)).length ≤ wordBound D := by
  have h := ProgramEncoding.encodeRecords_length_le (PackingProgram.inverseQueries D) D (by
    intro word hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    have hi' : i < D := by
      simpa only [List.mem_reverse, ← List.range_eq_range', List.mem_range] using hi
    simpa only [PackingMetadata.unary, List.length_replicate] using Nat.le_of_lt hi')
  simpa only [PackingProgram.inverseQueries, List.length_map, List.length_reverse,
    List.length_range', wordBound] using h

/-- The initial leftover state is obtained from the proved extraction output. -/
theorem context_snapshot (s : Spec U) :
    PackingOutputSemantics.snapshotOf (context s) =
      PackingOutputSemantics.packedSnapshot s.packing Fin.val s.encodeType := by
  exact PackingOutputSemantics.snapshotOf_extraction s.packing Fin.val s.encodeType
    (PackingProgram.initialExtraction (entries s) s.packing.blockCount) rfl rfl rfl rfl rfl

theorem context_address_length_le (s : Spec U) : (context s).address.length ≤ s.params.D := by
  have h := congrArg PackingLeftovers.Snapshot.address (context_snapshot s)
  change (context s).address.length = (PackingReorder.packedVertices s.packing).length at h
  rw [h]
  exact packed_vertices_length_le s

theorem context_metadata_length_le (s : Spec U) :
    (context s).metadata.length ≤ metadataBound s.params.D s.params.typeStream.length := by
  rw [context_metadata s]
  exact covered_length_le s

theorem context_addresses_length_le (s : Spec U) :
    (context s).addresses.length ≤ addressBound s.params.D := by
  have h := congrArg PackingLeftovers.Snapshot.addresses (context_snapshot s)
  change (context s).addresses = SelectorProgram.rawRecords
    (PackingAddressSemantics.addressRows
      ((PackingReorder.packedVertices s.packing).map s.encodeVertex) 0).reverse at h
  rw [h]
  exact address_list_length_le s (PackingReorder.packedVertices s.packing)
    (PackingAddressSemantics.packedVertices_nodup s.packing) (packed_vertices_length_le s)

def leftoversPolynomial (D T : ℕ) : ℕ :=
  36 + D * ((45 * D + 109) * metadataBound D T + 123 * D + 155) +
    10 * D + 8 * metadataBound D T + 6 * addressBound D + 3 * wordBound D

def inversePolynomial (D : ℕ) : ℕ :=
  6 * D ^ 2 + 19 * D + 33 + 12 * wordBound D + 9 * addressBound D +
    500 * (addressBound D + 1) * (wordBound D + 1)

theorem leftovers_budget_le (s : Spec U) :
    PackingProgram.leftoversBudget (covered s) s.params.D (context s) ≤
      leftoversPolynomial s.params.D s.params.typeStream.length := by
  let f := PackingProgram.leftoverResult (covered s) s.params.D (context s)
  obtain ⟨hm, ha, hs, hr⟩ := leftover_outputs s
  have hmeta : f.metadata.length ≤ metadataBound s.params.D s.params.typeStream.length := by
    rw [hm]
    exact metadata_length_le s
  have haddrs : f.addresses.length ≤ addressBound s.params.D := by
    rw [ha]
    exact addresses_length_le s
  have hstorage : f.storage.length ≤ wordBound s.params.D := by
    have hlen := congrArg List.length hs
    simp only [List.length_append, List.length_reverse, List.length_singleton] at hlen
    change f.storage.length + 1 = s.storage.length at hlen
    have hb := storage_length_le s
    omega
  have hrank : f.rank ≤ s.params.D := by rw [hr]; exact leftovers_length_le s
  have hinit := context_address_length_le s
  have hcovered := covered_length_le s
  have hcount : (PackingLeftovers.leftovers (covered s) (List.range s.params.D)).length ≤
      s.params.D := by
    exact (List.length_filter_le _ _).trans (by simp)
  have hcounter := (PackingLeftovers.final_counters (covered s) (List.range s.params.D)
    (PackingOutputSemantics.snapshotOf (context s))).2
  change f.address = (context s).address.length +
    (PackingLeftovers.leftovers (covered s) (List.range s.params.D)).length at hcounter
  have haddress : f.address ≤ 2 * s.params.D := by omega
  have ht := PackingLeftovers.range_traceCost_le (covered s) s.params.D
    (PackingOutputSemantics.snapshotOf (context s))
  have ht' : PackingLeftovers.traceCost (covered s) (List.range s.params.D)
      (PackingOutputSemantics.snapshotOf (context s)) ≤
      4 + s.params.D * ((45 * s.params.D + 109) *
        metadataBound s.params.D s.params.typeStream.length + 123 * s.params.D + 155) := by
    calc
      _ ≤ 4 + s.params.D * ((45 * s.params.D + 109) *
        (SelectorProgram.rawRecords (covered s)).length + 62 * s.params.D +
        31 * s.params.D + 15 * ((context s).address.length + s.params.D) + 155) := by
          simpa only [PackingOutputSemantics.snapshotOf, Nat.zero_add] using ht
      _ ≤ 4 + s.params.D * ((45 * s.params.D + 109) *
        metadataBound s.params.D s.params.typeStream.length + 62 * s.params.D +
        31 * s.params.D + 15 * (s.params.D + s.params.D) + 155) := by gcongr
      _ = _ := by ring
  change PackingLeftovers.traceCost (covered s) (List.range s.params.D)
      (PackingOutputSemantics.snapshotOf (context s)) + 6 * f.rank + 6 * f.metadata.length +
      6 * f.addresses.length + 3 * f.storage.length +
      2 * (SelectorProgram.rawRecords (covered s)).length + 2 * f.address + 32 ≤ _
  unfold leftoversPolynomial
  omega

theorem inverse_budget_le (s : Spec U) :
    PackingProgram.inverseBudget (addressRecords s) s.params.D ≤ inversePolynomial s.params.D := by
  have ha := address_records_length_le s
  have hq := queries_length_le s.params.D
  have hi : (ProgramEncoding.encodeRecords
      (PackingProgram.inverseRows (addressRecords s) s.params.D)).length ≤ wordBound s.params.D := by
    rw [inverse_rows s]
    exact inverse_length_le s
  have hsel : SelectorMapProgram.budget (addressRecords s) (PackingProgram.inverseQueries s.params.D) ≤
      500 * (addressBound s.params.D + 1) * (wordBound s.params.D + 1) := by
    calc
      _ ≤ 500 * ((SelectorProgram.rawRecords (addressRecords s)).length + 1) *
        ((ProgramEncoding.encodeRecords (PackingProgram.inverseQueries s.params.D)).length + 1) :=
          SelectorMapProgram.budget_bound _ _
      _ ≤ _ := by gcongr
  unfold PackingProgram.inverseBudget inversePolynomial
  omega

/-- Both actual tail stages have a fixed fourth-degree bound in the vertex
count and the bytes of the generated type stream. -/
theorem tail_budget_le (s : Spec U) :
    PackingProgram.leftoversBudget (covered s) s.params.D (context s) +
      PackingProgram.inverseBudget (addressRecords s) s.params.D ≤
      30000 * (s.params.D + s.params.typeStream.length + 1) ^ 4 := by
  let N := s.params.D + s.params.typeStream.length + 1
  have hD : s.params.D ≤ N := by dsimp [N]; omega
  have hT : s.params.typeStream.length ≤ N := by dsimp [N]; omega
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hp (k : ℕ) : N ^ k ≤ N ^ (k + 1) := by
    rw [pow_succ]
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (N ^ k) hN
  have h01 : 1 ≤ N := hN
  have h12 : N ≤ N ^ 2 := by simpa using hp 1
  have h23 : N ^ 2 ≤ N ^ 3 := hp 2
  have h34 : N ^ 3 ≤ N ^ 4 := hp 3
  calc
    _ ≤ leftoversPolynomial s.params.D s.params.typeStream.length + inversePolynomial s.params.D :=
      Nat.add_le_add (leftovers_budget_le s) (inverse_budget_le s)
    _ ≤ leftoversPolynomial N N + inversePolynomial N := by
      unfold leftoversPolynomial inversePolynomial metadataBound addressBound wordBound
      gcongr
    _ = 4450 * N ^ 4 + 7450 * N ^ 3 + 8171 * N ^ 2 + 3308 * N + 1084 := by
      unfold leftoversPolynomial inversePolynomial metadataBound addressBound wordBound
      ring
    _ ≤ 30000 * N ^ 4 := by omega

end SubexponentialSAT.Subexp.PackingTailBounds

end OAI.Algorithms
