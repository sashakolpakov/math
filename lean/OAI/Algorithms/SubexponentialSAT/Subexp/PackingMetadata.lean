import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingReorder
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisMetadata

namespace OAI.Algorithms

/-! Exact lookup semantics for the storage-ordered packing metadata table.
The physical extraction proof identifies its emitted records with this table. -/

namespace SubexponentialSAT.Subexp.PackingMetadata

open ConstructivePacking
open GlobalBasisMetadata (Metadata)

def unary (n : ℕ) : List Bool := List.replicate n true

theorem unary_injective : Function.Injective unary := by
  intro a b h
  simpa [unary] using congrArg List.length h

theorem unary_fin_eq_iff {n : ℕ} (a b : Fin n) : unary a.val = unary b.val ↔ a = b := by
  constructor
  · intro h
    exact Fin.ext (unary_injective h)
  · rintro rfl
    rfl

theorem frame_injective : Function.Injective Encoding.frame := by
  intro a b h
  exact (Encoding.frame_append_injective (rest := []) (rest' := []) (by simpa using h)).1

theorem metadata_encode_injective : Function.Injective Metadata.encode := by
  intro a b h
  cases a with
  | covered block typeCode =>
    cases b with
    | covered block' typeCode' =>
      have ht : Encoding.frame block ++ Encoding.frame typeCode =
          Encoding.frame block' ++ Encoding.frame typeCode' := (List.cons.inj h).2
      obtain ⟨hb, hu⟩ := Encoding.frame_append_injective ht
      cases hb
      cases frame_injective hu
      rfl
    | leftover rank =>
      have hf : true = false := (List.cons.inj h).1
      cases hf
  | leftover rank =>
    cases b with
    | covered block typeCode =>
      have hf : false = true := (List.cons.inj h).1
      cases hf
    | leftover rank' =>
      have ht : Encoding.frame rank = Encoding.frame rank' := (List.cons.inj h).2
      cases frame_injective ht
      rfl

variable {V U : Type*} [DecidableEq V] [DecidableEq U]

def value (P : PackingData V U) (encodeType : U → List Bool) (v : V) : Metadata :=
  match P.lookup v with
  | some z => .covered (unary z.1.val) (encodeType z.2)
  | none => .leftover (unary (P.leftovers.idxOf v))

def row (P : PackingData V U) (encodeVertex : V → List Bool)
    (encodeType : U → List Bool) (v : V) : List Bool × List Bool :=
  (encodeVertex v, (value P encodeType v).encode)

/-- The actual emitter prepends pairs while traversing storage order. -/
def records (P : PackingData V U) (encodeVertex : V → List Bool)
    (encodeType : U → List Bool) : List (List Bool × List Bool) :=
  (PackingReorder.storageVertices P).reverse.map (row P encodeVertex encodeType)

def coveredRecords (P : PackingData V U) (encodeVertex : V → List Bool)
    (encodeType : U → List Bool) : List (List Bool × List Bool) :=
  (PackingReorder.packedVertices P).reverse.map (row P encodeVertex encodeType)

theorem records_eq_leftovers_append (P : PackingData V U)
    (encodeVertex : V → List Bool) (encodeType : U → List Bool) :
    records P encodeVertex encodeType =
      P.leftovers.reverse.map (row P encodeVertex encodeType) ++
        coveredRecords P encodeVertex encodeType := by
  simp [records, coveredRecords, PackingReorder.storageVertices, List.reverse_append]

theorem lookup_graph_encoded {A B : Type*} [DecidableEq A]
    (xs : List A) (key : A → List Bool) (f : A → B)
    (hkey : Function.Injective key) (a : A) (ha : a ∈ xs) :
    (xs.map (fun x => (key x, f x))).lookup (key a) = some (f a) := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    by_cases h : a = x
    · subst x
      simp
    · have hk : key a ≠ key x := fun he => h (hkey he)
      simpa [List.lookup_cons, beq_false_of_ne hk] using
        ih (List.mem_of_ne_of_mem h ha)

theorem lookup_graph_encoded_none {A B : Type*} [DecidableEq A]
    (xs : List A) (key : A → List Bool) (f : A → B)
    (hkey : Function.Injective key) (a : A) :
    (xs.map (fun x => (key x, f x))).lookup (key a) = none ↔ a ∉ xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases h : a = x
    · subst x
      simp
    · have hk : key a ≠ key x := fun he => h (hkey he)
      simp [List.lookup_cons, beq_false_of_ne hk, h, ih]

theorem lookup_eq (P : PackingData V U) (encodeVertex : V → List Bool)
    (encodeType : U → List Bool) (hvertex : Function.Injective encodeVertex) (v : V) :
    (records P encodeVertex encodeType).lookup (encodeVertex v) =
      some (value P encodeType v).encode :=
  lookup_graph_encoded _ _ _ hvertex v
    (by simpa using PackingReorder.mem_storageVertices P v)

@[simp] theorem value_at (P : PackingData V U) (encodeType : U → List Bool)
    (i : Fin P.blockCount) (u : U) :
    value P encodeType (P.vertexAt i u) = .covered (unary i.val) (encodeType u) := by
  simp [value]

theorem value_eq_covered_iff (P : PackingData V U) (encodeType : U → List Bool)
    (htype : Function.Injective encodeType) (v : V) (i : Fin P.blockCount) (u : U) :
    value P encodeType v = .covered (unary i.val) (encodeType u) ↔
      P.lookup v = some (i, u) := by
  cases hv : P.lookup v with
  | none => simp [value, hv]
  | some z =>
    rcases z with ⟨j, w⟩
    simp [value, hv, unary_fin_eq_iff, htype.eq_iff]

/-- Covered metadata identifies exactly the computed block/type inverse. -/
theorem lookup_covered_iff (P : PackingData V U)
    (encodeVertex : V → List Bool) (encodeType : U → List Bool)
    (hvertex : Function.Injective encodeVertex) (htype : Function.Injective encodeType)
    (v : V) (i : Fin P.blockCount) (u : U) :
    (records P encodeVertex encodeType).lookup (encodeVertex v) =
      some (Metadata.covered (unary i.val) (encodeType u)).encode ↔
      P.lookup v = some (i, u) := by
  rw [lookup_eq P encodeVertex encodeType hvertex]
  simp only [Option.some.injEq, metadata_encode_injective.eq_iff]
  exact value_eq_covered_iff P encodeType htype v i u

/-- An uncovered vertex carries its actual rank in the original-order leftover list. -/
theorem lookup_leftover (P : PackingData V U)
    (encodeVertex : V → List Bool) (encodeType : U → List Bool)
    (hvertex : Function.Injective encodeVertex) (v : V) (hv : P.lookup v = none) :
    (records P encodeVertex encodeType).lookup (encodeVertex v) =
      some (Metadata.leftover (unary (P.leftovers.idxOf v))).encode := by
  rw [lookup_eq P encodeVertex encodeType hvertex]
  simp [value, hv]

theorem mem_packedVertices_iff (P : PackingData V U) (v : V) :
    v ∈ PackingReorder.packedVertices P ↔ ∃ z, P.lookup v = some z := by
  constructor
  · intro hv
    obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hv
    obtain ⟨u, _, hu⟩ := List.mem_map.mp hi
    refine ⟨(i, u), ?_⟩
    rw [← hu]
    exact P.lookup_at i u
  · rintro ⟨z, hz⟩
    apply List.mem_flatMap.mpr
    refine ⟨z.1, by simp, ?_⟩
    exact List.mem_map.mpr ⟨z.2, P.types.complete _, P.lookup_sound v z hz⟩

theorem covered_lookup_none_iff (P : PackingData V U)
    (encodeVertex : V → List Bool) (encodeType : U → List Bool)
    (hvertex : Function.Injective encodeVertex) (v : V) :
    (coveredRecords P encodeVertex encodeType).lookup (encodeVertex v) = none ↔
      P.lookup v = none := by
  unfold coveredRecords row
  rw [lookup_graph_encoded_none _ _ _ hvertex, List.mem_reverse, mem_packedVertices_iff]
  cases hv : P.lookup v <;> simp []

/-- The physical missing-key filter selects exactly the typed leftovers. -/
theorem covered_filter_eq_leftovers (P : PackingData V U)
    (encodeVertex : V → List Bool) (encodeType : U → List Bool)
    (hvertex : Function.Injective encodeVertex) :
    P.vertices.values.filter (fun v => decide
      ((coveredRecords P encodeVertex encodeType).lookup (encodeVertex v) = none)) = P.leftovers := by
  unfold PackingData.leftovers
  apply List.filter_congr
  intro v _
  simp only [covered_lookup_none_iff P encodeVertex encodeType hvertex]

end SubexponentialSAT.Subexp.PackingMetadata

end OAI.Algorithms
