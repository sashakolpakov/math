import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendCore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramNativeCost

namespace OAI.Algorithms

/-! Uniform physical-input capacity for the produced per-query frontend data. -/
namespace SubexponentialSAT.SqrtLog.LeafScopeInputBounds
open LeafQueryFrontend

def capacity (q : Query) (k : ℕ) : ℕ :=
  BinaryArithmetic.toNat q.ambient + (Encoding.encodeList id q.clauses).length +
    (HashScopeProgram.RawTable.inputBits q.width.length q.rows).length + q.index.length +
    q.modulus.length + q.width.length + q.ambient.length + k + 8

structure QueryBounds (q : Query) (k : ℕ) : Prop where
  eight : 8 ≤ capacity q k
  ambient : BinaryArithmetic.toNat q.ambient ≤ capacity q k
  master : (Encoding.encodeList id q.clauses).length ≤ capacity q k
  rowBits : (HashScopeProgram.RawTable.inputBits q.width.length q.rows).length ≤ capacity q k
  index : q.index.length ≤ capacity q k
  modulus : q.modulus.length ≤ capacity q k
  width : q.width.length ≤ capacity q k
  ambientBits : q.ambient.length ≤ capacity q k
  widthParameter : k ≤ capacity q k
  clauseCount : q.clauses.length ≤ capacity q k
  rawRowCount : q.rows.length ≤ capacity q k
  rawRowSlots : ∀ row ∈ q.rows, row.length ≤ capacity q k
  scopeCount : q.scopeRows.length ≤ capacity q k
  scopeSlots : ∀ row ∈ q.scopeRows, row.length ≤ capacity q k
  scopeMass : LeafScopeResourceBounds.slots q.scopeRows ≤ (capacity q k)^2
  scopeBits : (LeafStatisticsProgram.scopeBits q.scopeRows).length ≤ 16*(capacity q k)^3
  forward : q.forward.length ≤ capacity q k
  free : (totals q.scopeRows q.forward).free ≤ capacity q k
  occurrence : (totals q.scopeRows q.forward).occurrence ≤ capacity q k
  incidences : (totals q.scopeRows q.forward).incidences ≤ 2*(capacity q k)^2
  uncovered : (totals q.scopeRows q.forward).uncovered ≤ capacity q k
  arity : completedArity q.scopeRows q.forward ≤ capacity q k
  factors : q.scopeRows.length+(totals q.scopeRows q.forward).uncovered ≤ 2*capacity q k

theorem scope_count_le_rows (q : Query) :
    q.scopeRows.length ≤ (HashScopeProgram.RawTable.inputBits q.width.length q.rows).length := by
  have h := Encoding.length_encodeList_lower id (q.rows.map (HashScopeProgram.RawTable.rowBits q.width.length))
  have hm : q.mark.isSome.toNat ≤ 1 := by cases q.mark <;> simp
  change (HashScopeProgram.Complete.scopes 1 0 q.codes q.rows q.mark).length ≤ _
  rw [HashScopeProgram.Complete.scopes_length]
  simpa only [HashScopeProgram.RawTable.inputBits, List.length_map] using
    (show q.rows.length+q.mark.isSome.toNat ≤
      (Encoding.encodeList id (q.rows.map (HashScopeProgram.RawTable.rowBits q.width.length))).length by
      simp only [List.length_map] at h
      omega)

theorem raw_row_slots_le_rows (q : Query) (hwidth : 0 < q.width.length)
    (row : List (Fin q.clauses.length × ZMod 3)) (hr : row ∈ q.rows) :
    row.length ≤ (HashScopeProgram.RawTable.inputBits q.width.length q.rows).length := by
  have hh := encoded_member_length id (q.rows.map (HashScopeProgram.RawTable.rowBits q.width.length))
    (HashScopeProgram.RawTable.rowBits q.width.length row) (List.mem_map.mpr ⟨row,hr,rfl⟩)
  have hl : row.length ≤ row.length*q.width.length := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left row.length (Nat.succ_le_of_lt hwidth)
  have he : (HashScopeProgram.RawTable.rowBits q.width.length row).length = row.length*q.width.length :=
    CodeRowsProgram.rowPayload_length q.width.length q.clauses.length row
  exact (hl.trans_eq he.symm).trans hh

theorem query_bounds (q : Query) (k : ℕ) (hv : q.Valid) : QueryBounds q k := by
  rcases hv with ⟨hw,hn,hcodes,hlarge,hindex,hmod,hids⟩
  have h8 : 8 ≤ capacity q k := by unfold capacity; omega
  have hS : 1 ≤ capacity q k := by omega
  have hamb : BinaryArithmetic.toNat q.ambient ≤ capacity q k := by unfold capacity; omega
  have hmaster : (Encoding.encodeList id q.clauses).length ≤ capacity q k := by unfold capacity; omega
  have hrows : (HashScopeProgram.RawTable.inputBits q.width.length q.rows).length ≤ capacity q k := by unfold capacity; omega
  have hclause : q.clauses.length ≤ capacity q k :=
    (Nat.le_of_succ_le (Encoding.length_encodeList_lower id q.clauses)).trans hmaster
  have hraw : q.rows.length ≤ capacity q k := by
    have h := Encoding.length_encodeList_lower id (q.rows.map (HashScopeProgram.RawTable.rowBits q.width.length))
    simp only [List.length_map] at h
    exact (Nat.le_of_succ_le h).trans hrows
  have hscope : q.scopeRows.length ≤ capacity q k := (scope_count_le_rows q).trans hrows
  have hd : ∀ row ∈ q.scopeRows, row.Nodup := LeafScopeResourceBounds.scopes_nodup 1 0 q.codes q.rows q.mark
  have hforward : q.forward.length = BinaryArithmetic.toNat q.ambient := by simp [Query.forward, highMask]
  have hs := statistics_bound q.scopeRows q.forward (BinaryArithmetic.toNat q.ambient) (capacity q k)
    hS hamb (hforward.le.trans hamb) hscope hd hids
  refine ⟨h8,hamb,hmaster,hrows,?_,?_,?_,?_,?_,hclause,hraw,?_,hscope,?_,?_,?_,
    hforward.le.trans hamb,hs.free,hs.occurrence,hs.incidences,hs.uncovered,hs.arity,hs.factors⟩
  · unfold capacity; omega
  · unfold capacity; omega
  · unfold capacity; omega
  · unfold capacity; omega
  · unfold capacity; omega
  · intro row hr
    exact (raw_row_slots_le_rows q hw row hr).trans hrows
  · intro row hr
    exact (finite_scope_length row _ (hd row hr) (hids row hr)).trans hamb
  · exact scope_mass q.scopeRows _ _ hamb hscope hd hids
  · exact scope_wire q.scopeRows _ _ hS hamb hscope hd hids

/-- The existing fixed scope-producer polynomial receives the same input-only
capacity as the downstream scan and parameter bounds. -/
theorem scope_cost_le (q : Query) (k : ℕ) (hv : q.Valid) :
    HashScopeProgram.Complete.cost 1 0 q.width.length q.modulus q.clauses q.codes q.rows q.mark q.index ≤
      HashScopeProgram.Complete.polynomialBound (capacity q k) := by
  have h := query_bounds q k hv
  have hlog : Nat.log 2 3 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
  have hweight : (0+1)*SubexpLiftRing.baseWidth 3 1 ≤ capacity q k := by
    have hh : (0+1)*SubexpLiftRing.baseWidth 3 1 ≤ 8 := by norm_num [SubexpLiftRing.baseWidth, hlog]
    exact hh.trans h.eight
  exact HashScopeProgram.Complete.cost_le_polynomial 1 0 q.width.length q.modulus q.clauses q.codes
    hv.2.2.1 q.rows q.mark q.index (capacity q k) (by have := h.eight; omega)
    h.rawRowCount h.rawRowSlots h.width h.modulus h.clauseCount h.master hweight h.index

end SubexponentialSAT.SqrtLog.LeafScopeInputBounds

end OAI.Algorithms
