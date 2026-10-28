import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBoundsUniform

namespace OAI.Algorithms

/-! Input-size bounds for explicit scopes. These bounds use actual duplicate-free
original-coordinate scope rows, with no value-only replacement for their bytes. -/
namespace SubexponentialSAT.SqrtLog.LeafScopeInputBounds
open LeafStatisticsProgram LeafStatisticsSemantics

/-- A field occupies no more bytes than its containing framed list. -/
theorem encoded_member_length {α : Type*} (encode : α → List Bool)
    (rows : List α) (a : α) (ha : a ∈ rows) :
    (encode a).length ≤ (Encoding.encodeList encode rows).length := by
  induction rows with
  | nil => simp at ha
  | cons b bs ih =>
    rw [Encoding.length_encodeList_cons]
    rcases List.mem_cons.mp ha with rfl | ha
    · omega
    · have h := ih ha
      omega

theorem finite_scope_length (row : List ℕ) (n : ℕ) (hd : row.Nodup)
    (hi : ∀ v ∈ row, v < n) : row.length ≤ n := by
  classical
  rw [← List.toFinset_card_of_nodup hd]
  calc
    row.toFinset.card ≤ (Finset.range n).card := Finset.card_le_card (by
      intro v hv
      exact Finset.mem_range.mpr (hi v (List.mem_toFinset.mp hv)))
    _ = n := Finset.card_range n

/-- Unary original IDs are explicitly charged in each serialized scope row. -/
theorem scope_row_wire (row : List ℕ) (n S : ℕ) (hS : 1 ≤ S) (hn : n ≤ S)
    (hd : row.Nodup) (hi : ∀ v ∈ row, v < n) :
    (Encoding.encodeList Encoding.encodeNat row).length ≤ 5*S^2 := by
  have hl := (finite_scope_length row n hd hi).trans hn
  have hw := Encoding.length_encodeList_upper Encoding.encodeNat row S (by
    intro v hv
    rw [Encoding.length_encodeNat]
    exact (Nat.succ_le_of_lt (hi v hv)).trans hn)
  calc
    _ ≤ 1+(2*S+2)*S := hw.trans (by gcongr)
    _ ≤ 5*S^2 := by nlinarith

theorem scope_wire (scopes : List (List ℕ)) (n S : ℕ) (hS : 1 ≤ S)
    (hn : n ≤ S) (hc : scopes.length ≤ S)
    (hd : ∀ row ∈ scopes, row.Nodup) (hi : ∀ row ∈ scopes, ∀ v ∈ row, v < n) :
    (scopeBits scopes).length ≤ 16*S^3 := by
  have hw := Encoding.length_encodeList_upper (Encoding.encodeList Encoding.encodeNat) scopes
    (5*S^2) (fun row hr => scope_row_wire row n S hS hn (hd row hr) (hi row hr))
  have hp : 1 ≤ S^2 := Nat.one_le_pow _ _ hS
  have hcube : S ≤ S^3 := by
    simpa [pow_succ, Nat.mul_comm] using Nat.mul_le_mul_left S hp
  calc
    _ ≤ 1+(2*(5*S^2)+2)*S := hw.trans (by gcongr)
    _ ≤ 16*S^3 := by nlinarith only [hcube,hS]

theorem scope_mass (scopes : List (List ℕ)) (n S : ℕ)
    (hn : n ≤ S) (hc : scopes.length ≤ S)
    (hd : ∀ row ∈ scopes, row.Nodup) (hi : ∀ row ∈ scopes, ∀ v ∈ row, v < n) :
    LeafScopeResourceBounds.slots scopes ≤ S^2 := by
  have h := LeafScopeResourceBounds.slots_le scopes n
    (fun row hr => finite_scope_length row n (hd row hr) (hi row hr))
  exact h.trans (by simpa [pow_two] using Nat.mul_le_mul hc hn)

theorem occurrence_le_rows (scopes : List (List ℕ)) (mask : List Bool) :
    (measured scopes mask).occurrence ≤ max 1 scopes.length := by
  apply (totals_occurrence_le_iff scopes 0 mask zero _).mpr
  refine ⟨Nat.zero_le _, ?_⟩
  intro i _
  apply max_le_max_left
  simpa only [Subexp.IncidencePlanSpec.degree, Subexp.IncidencePlanSpec.incidentIndices,
    Nat.zero_add] using SubexpIncidencePlanScan.incidenceFrom_length_le i.val 0 scopes

structure StatisticsBound (scopes : List (List ℕ)) (mask : List Bool) (S : ℕ) : Prop where
  free : (measured scopes mask).free ≤ S
  occurrence : (measured scopes mask).occurrence ≤ S
  incidences : (measured scopes mask).incidences ≤ 2*S^2
  uncovered : (measured scopes mask).uncovered ≤ S
  arity : max (Arity.arity mask scopes 0)
    (if (measured scopes mask).uncovered=0 then 0 else 1) ≤ S
  factors : scopes.length+(measured scopes mask).uncovered ≤ 2*S

theorem statistics_bound (scopes : List (List ℕ)) (mask : List Bool) (n S : ℕ)
    (hS : 1 ≤ S) (hn : n ≤ S) (hm : mask.length ≤ S) (hc : scopes.length ≤ S)
    (hd : ∀ row ∈ scopes, row.Nodup) (hi : ∀ row ∈ scopes, ∀ v ∈ row, v < n) :
    StatisticsBound scopes mask S := by
  have hf := (free_le_ambient scopes mask).trans hm
  have hu := (LeafScopeResourceBounds.measured_uncovered_le scopes mask).trans hm
  have ho := (occurrence_le_rows scopes mask).trans (max_le hS hc)
  have ha := (LeafScopeResourceBounds.measured_arity_le scopes mask n
    (fun row hr => finite_scope_length row n (hd row hr) (hi row hr))).trans (max_le hn hS)
  have hs := scope_mass scopes n S hn hc hd hi
  have hM := LeafScopeResourceBounds.measured_incidences_le scopes mask
  have hsquare : S ≤ S^2 := by nlinarith
  refine ⟨hf,ho,?_,hu,ha,?_⟩
  · omega
  · omega

end SubexponentialSAT.SqrtLog.LeafScopeInputBounds

end OAI.Algorithms
