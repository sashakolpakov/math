import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking
import OAI.Algorithms.SubexponentialSAT.ComputablePackingSplit
import OAI.Algorithms.SubexponentialSAT.ArrayUpdatePrograms

namespace OAI.Algorithms

/-!
# Represented reordering of packed coordinates

The input table contains block-major scalar records followed by the residual
coordinate records. A concrete `idxOf` plan reorders this table into the original
vertex order. The value proof connects the represented records with the actual
computable packing split; the fixed gathering program executes the read plan.
-/

namespace SubexponentialSAT.Subexp.PackingReorder

open ConstructivePacking

variable {V U : Type*} [DecidableEq V] [DecidableEq U]

/-- Coordinates in the same block-major order as the copied local tables. -/
def packedVertices (P : PackingData V U) : List V :=
  (List.finRange P.blockCount).flatMap fun i => P.types.values.map (P.vertexAt i)

/-- Actual input-table coordinate order: complete blocks, then leftovers. -/
def storageVertices (P : PackingData V U) : List V :=
  packedVertices P ++ P.leftovers

/-- Explicit index plan; it is data, not part of the finite program control. -/
def readPlan (P : PackingData V U) : List ℕ :=
  P.vertices.values.map (storageVertices P).idxOf

/-- A vertex obtains its record from its computed block position or its
residual value. The same executable lookup is used to construct the packing. -/
def assembledRecord (P : PackingData V U)
    (blocks : Fin P.blockCount → U → List Bool) (residual : V → List Bool)
    (v : V) : List Bool :=
  match P.lookup v with
  | some z => blocks z.1 z.2
  | none => residual v

/-- The represented table before reordering. -/
def records (P : PackingData V U)
    (blocks : Fin P.blockCount → U → List Bool) (residual : V → List Bool) :
    List (List Bool) :=
  ((List.finRange P.blockCount).flatMap fun i => P.types.values.map (blocks i)) ++
    P.leftovers.map residual

theorem mem_storageVertices (P : PackingData V U) (v : V) :
    v ∈ storageVertices P := by
  cases hv : P.lookup v with
  | none =>
      apply List.mem_append_right
      exact (P.mem_leftovers v).mpr ((P.lookup_none_iff v).mp hv)
  | some z =>
      apply List.mem_append_left
      apply List.mem_flatMap.mpr
      refine ⟨z.1, by simp, ?_⟩
      exact List.mem_map.mpr ⟨z.2, P.types.complete _, P.lookup_sound v z hv⟩

theorem records_eq_storage_map (P : PackingData V U)
    (blocks : Fin P.blockCount → U → List Bool) (residual : V → List Bool) :
    records P blocks residual =
      (storageVertices P).map (assembledRecord P blocks residual) := by
  unfold records storageVertices packedVertices
  rw [List.map_append, List.map_flatMap]
  apply congrArg₂ List.append
  · apply congrArg (fun f => (List.finRange P.blockCount).flatMap f)
    funext i
    rw [List.map_map]
    apply List.map_congr_left
    intro u _
    simp [assembledRecord]
  · apply List.map_congr_left
    intro v hv
    have hn := (P.lookup_none_iff v).mpr ((P.mem_leftovers v).mp hv)
    simp [assembledRecord, hn]

private theorem getD_map_idxOf {A B : Type*} [DecidableEq A]
    (xs : List A) (f : A → B) (v : A) (hv : v ∈ xs) (d : B) :
    (xs.map f).getD (xs.idxOf v) d = f v := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_idxOf hv, Option.map_some, Option.getD_some]

/-- Functional specification of the fixed gathering program. -/
def gatherRows (rows : List (List Bool)) (plan : List ℕ) : List Bool :=
  plan.flatMap (fun i => rows.getD i [])

/-- Exact represented output in original vertex order. -/
theorem gathered_records (P : PackingData V U)
    (blocks : Fin P.blockCount → U → List Bool) (residual : V → List Bool) :
    gatherRows (records P blocks residual) (readPlan P) =
      P.vertices.values.flatMap (assembledRecord P blocks residual) := by
  rw [records_eq_storage_map]
  simp only [gatherRows, readPlan, List.flatMap_map]
  apply congrArg (fun f => P.vertices.values.flatMap f)
  funext v
  exact getD_map_idxOf _ _ _ (mem_storageVertices P v) _

theorem readPlan_valid (P : PackingData V U)
    (blocks : Fin P.blockCount → U → List Bool) (residual : V → List Bool) :
    ∀ i ∈ readPlan P, i < (records P blocks residual).length := by
  intro i hi
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hi
  rw [records_eq_storage_map, List.length_map]
  exact List.idxOf_lt_length_iff.mpr (mem_storageVertices P v)

@[simp] theorem readPlan_length (P : PackingData V U) :
    (readPlan P).length = P.vertices.values.length := by simp [readPlan]

omit [DecidableEq V] in
theorem packedVertices_length (P : PackingData V U) :
    (packedVertices P).length = P.blockCount * P.types.values.length := by
  simp [packedVertices, List.length_flatMap]

theorem storageVertices_length [Fintype V] [Fintype U] (P : PackingData V U) :
    (storageVertices P).length = P.vertices.values.length := by
  rw [storageVertices, List.length_append, packedVertices_length,
    P.types.length_eq_card, P.vertices.length_eq_card]
  have h := P.leftovers_length_add_packed
  omega

theorem records_length [Fintype V] [Fintype U] (P : PackingData V U)
    (blocks : Fin P.blockCount → U → List Bool) (residual : V → List Bool) :
    (records P blocks residual).length = P.vertices.values.length := by
  rw [records_eq_storage_map, List.length_map, storageVertices_length]

theorem assembledRecord_length (P : PackingData V U)
    (blocks : Fin P.blockCount → U → List Bool) (residual : V → List Bool) (w : ℕ)
    (hb : ∀ i u, (blocks i u).length = w) (hr : ∀ v, (residual v).length = w)
    (v : V) : (assembledRecord P blocks residual v).length = w := by
  unfold assembledRecord
  cases P.lookup v with
  | none => exact hr v
  | some z => exact hb z.1 z.2

theorem records_uniform (P : PackingData V U)
    (blocks : Fin P.blockCount → U → List Bool) (residual : V → List Bool) (w : ℕ)
    (hb : ∀ i u, (blocks i u).length = w) (hr : ∀ v, (residual v).length = w) :
    ∀ row ∈ records P blocks residual, row.length = w := by
  intro row hrow
  rw [records_eq_storage_map] at hrow
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hrow
  exact assembledRecord_length P blocks residual w hb hr v

theorem records_bit_length [Fintype V] [Fintype U] (P : PackingData V U)
    (blocks : Fin P.blockCount → U → List Bool) (residual : V → List Bool) (w : ℕ)
    (hb : ∀ i u, (blocks i u).length = w) (hr : ∀ v, (residual v).length = w) :
    (records P blocks residual).flatten.length = P.vertices.values.length * w := by
  rw [ArrayUpdatePrograms.uniform_flatten_length _ w
    (records_uniform P blocks residual w hb hr), records_length]

section Values

variable {K : Type*} [Semiring K] [Fintype U]

/-- The lookup-based represented value equals the proved coordinate assembly. -/
theorem assembledRecord_eq_encode_assemble (P : PackingData V U) (encode : K → List Bool)
    (blocks : Fin P.blockCount → U → K) (residual : V → K) (v : V) :
    assembledRecord P (fun i u => encode (blocks i u)) (fun a => encode (residual a)) v =
      encode (ComputablePackingSplit.assemble P.completeBlocks.embed
        (blocks, fun a => residual a.val) v) := by
  cases hv : P.lookup v with
  | none =>
      simp only [assembledRecord, hv]
      rw [ComputablePackingSplit.assemble_outside _ _ _ ((P.lookup_none_iff v).mp hv)]
  | some z =>
      simp only [assembledRecord, hv]
      have he := P.lookup_sound v z hv
      rw [← he]
      change encode (blocks z.1 z.2) =
        encode (ComputablePackingSplit.assemble P.completeBlocks.embed
          (blocks, fun a => residual a.val) (P.completeBlocks.embed (z.1, z.2)))
      rw [ComputablePackingSplit.assemble_on_block]

/-- End-to-end semantic refinement of represented reordering to the actual
linear reconstruction from blocks and residual coordinates. -/
theorem gathered_eq_encode_assemble (P : PackingData V U) (encode : K → List Bool)
    (blocks : Fin P.blockCount → U → K) (residual : V → K) :
    gatherRows
      (records P (fun i u => encode (blocks i u)) (fun a => encode (residual a)))
      (readPlan P) =
    P.vertices.values.flatMap (fun v =>
      encode (ComputablePackingSplit.assemble P.completeBlocks.embed
        (blocks, fun a => residual a.val) v)) := by
  rw [gathered_records]
  apply congrArg (fun f => P.vertices.values.flatMap f)
  funext v
  exact assembledRecord_eq_encode_assemble P encode blocks residual v

end Values

end SubexponentialSAT.Subexp.PackingReorder

end OAI.Algorithms
