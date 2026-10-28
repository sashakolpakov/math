import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingMetadata
import OAI.Algorithms.SubexponentialSAT.Subexp.SelectorMapProgram
import OAI.Algorithms.SubexponentialSAT.LocalExpectation

namespace OAI.Algorithms

/-! The emitted storage-address table is the graph of the actual packed
coordinate order. Its lookups produce the existing reordering read plan. -/

namespace SubexponentialSAT.Subexp.PackingAddressSemantics

open ConstructivePacking

variable {V U : Type*} [DecidableEq V] [DecidableEq U]

theorem packedVertices_nodup (P : PackingData V U) :
    (PackingReorder.packedVertices P).Nodup := by
  have hp : ((List.finRange P.blockCount).product P.types.values).Nodup :=
    (List.nodup_finRange P.blockCount).product P.types.nodup
  have hm := hp.map P.completeBlocks.embed.injective
  simpa only [List.product, List.map_flatMap, List.map_map, Function.comp_def,
    PackingData.completeBlocks_apply, PackingReorder.packedVertices] using hm

theorem packed_disjoint_leftovers (P : PackingData V U) :
    List.Disjoint (PackingReorder.packedVertices P) P.leftovers := by
  apply List.disjoint_left.mpr
  intro v hp hl
  obtain ⟨z, hz⟩ := (PackingMetadata.mem_packedVertices_iff P v).mp hp
  exact ((P.mem_leftovers v).mp hl) ⟨z, (P.lookup_some_iff v z).mp hz⟩

theorem storageVertices_nodup (P : PackingData V U) :
    (PackingReorder.storageVertices P).Nodup :=
  List.Nodup.append (packedVertices_nodup P) P.leftovers_nodup (packed_disjoint_leftovers P)

/-- The physical address emitter increments a unary counter once per key. -/
def addressRows (vertices : List (List Bool)) (start : ℕ) : List (List Bool × List Bool) :=
  vertices.zipWith (fun v i => (v, List.replicate i true))
    (List.range' start vertices.length)

@[simp] theorem addressRows_nil (start : ℕ) : addressRows [] start = [] := rfl

theorem addressRows_cons (v : List Bool) (vertices : List (List Bool)) (start : ℕ) :
    addressRows (v :: vertices) start =
      (v, List.replicate start true) :: addressRows vertices (start + 1) := by
  simp only [addressRows, List.length_cons, List.range'_succ, List.zipWith_cons_cons]

theorem addressRows_append (left right : List (List Bool)) (start : ℕ) :
    addressRows (left ++ right) start =
      addressRows left start ++ addressRows right (start + left.length) := by
  induction left generalizing start with
  | nil => simp
  | cons v left ih =>
    simp only [List.cons_append, addressRows_cons, ih, List.length_cons]
    simp only [ Nat.add_comm, Nat.add_left_comm]

@[simp] theorem addressRows_length (vertices : List (List Bool)) (start : ℕ) :
    (addressRows vertices start).length = vertices.length := by
  simp [addressRows]

theorem addressRows_map_graph {A : Type*} [DecidableEq A] (vertices : List A)
    (encode : A → List Bool) (hn : vertices.Nodup) :
    addressRows (vertices.map encode) 0 =
      vertices.map (fun v => (encode v, List.replicate (vertices.idxOf v) true)) := by
  unfold addressRows
  rw [List.length_map, ← List.range_eq_range',
    ← SubexponentialSAT.LocalExpectation.map_idxOf_eq_range vertices hn,
    List.zipWith_map, List.zipWith_self]
  simp only [SubexponentialSAT.LocalExpectation.indexCode]

theorem addressRows_graph (vertices : List (List Bool)) (hn : vertices.Nodup) :
    addressRows vertices 0 =
      vertices.map (fun v => (v, List.replicate (vertices.idxOf v) true)) := by
  simpa only [List.map_id, id_eq, List.idxOf, Bool.beq_eq_decide_eq] using
    addressRows_map_graph vertices id hn

theorem lookup_reverse_addressRows {A : Type*} [DecidableEq A] (vertices : List A)
    (encode : A → List Bool) (hn : vertices.Nodup) (he : Function.Injective encode)
    (v : A) (hv : v ∈ vertices) :
    ((addressRows (vertices.map encode) 0).reverse).lookup (encode v) =
      some (List.replicate (vertices.idxOf v) true) := by
  rw [addressRows_map_graph vertices encode hn, ← List.map_reverse]
  exact PackingMetadata.lookup_graph_encoded vertices.reverse encode
    (fun v => List.replicate (vertices.idxOf v) true) he v (by simpa using hv)

/-- This is the reversed table retained by the physical emitter. -/
def storageAddresses (P : PackingData V U) (encodeVertex : V → List Bool) :
    List (List Bool × List Bool) :=
  (addressRows ((PackingReorder.storageVertices P).map encodeVertex) 0).reverse

theorem lookup_storageAddresses (P : PackingData V U) (encodeVertex : V → List Bool)
    (he : Function.Injective encodeVertex) (v : V) :
    (storageAddresses P encodeVertex).lookup (encodeVertex v) =
      some (List.replicate ((PackingReorder.storageVertices P).idxOf v) true) :=
  lookup_reverse_addressRows _ encodeVertex (storageVertices_nodup P) he v
    (PackingReorder.mem_storageVertices P v)

theorem selected_storageAddresses (P : PackingData V U) (encodeVertex : V → List Bool)
    (he : Function.Injective encodeVertex) (v : V) :
    SelectorMapProgram.selected (storageAddresses P encodeVertex) (encodeVertex v) =
      List.replicate ((PackingReorder.storageVertices P).idxOf v) true := by
  unfold SelectorMapProgram.selected
  rw [lookup_storageAddresses P encodeVertex he v]
  rfl

theorem selected_queries_eq_readPlan (P : PackingData V U) (encodeVertex : V → List Bool)
    (he : Function.Injective encodeVertex) :
    (P.vertices.values.map encodeVertex).map
      (SelectorMapProgram.selected (storageAddresses P encodeVertex)) =
      (PackingReorder.readPlan P).map (fun i => List.replicate i true) := by
  simp only [PackingReorder.readPlan, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro v _
  exact selected_storageAddresses P encodeVertex he v

/-- Reverse queries compensate for the selector's prepending accumulator,
so its actual output is the read plan in original vertex order. -/
theorem mappedRecords_eq_readPlan (P : PackingData V U) (encodeVertex : V → List Bool)
    (he : Function.Injective encodeVertex) :
    SelectorMapProgram.mappedRecords (storageAddresses P encodeVertex)
      (P.vertices.values.reverse.map encodeVertex) =
      (PackingReorder.readPlan P).map (fun i => List.replicate i true) := by
  unfold SelectorMapProgram.mappedRecords
  rw [List.map_reverse, List.map_reverse, List.reverse_reverse]
  exact selected_queries_eq_readPlan P encodeVertex he

end SubexponentialSAT.Subexp.PackingAddressSemantics

end OAI.Algorithms
